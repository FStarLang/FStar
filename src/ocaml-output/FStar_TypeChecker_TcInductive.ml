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
          let uu____61418 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____61418 with
           | (usubst,uvs1) ->
               let uu____61445 =
                 let uu____61452 =
                   FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                 let uu____61453 =
                   FStar_Syntax_Subst.subst_binders usubst tps  in
                 let uu____61454 =
                   let uu____61455 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____61455 k  in
                 (uu____61452, uu____61453, uu____61454)  in
               (match uu____61445 with
                | (env1,tps1,k1) ->
                    let uu____61475 = FStar_Syntax_Subst.open_term tps1 k1
                       in
                    (match uu____61475 with
                     | (tps2,k2) ->
                         let uu____61490 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____61490 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____61511 =
                                let uu____61530 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____61530 with
                                | (k3,uu____61556,g) ->
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
                                    let uu____61559 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____61574 =
                                      let uu____61575 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____61575
                                       in
                                    (uu____61559, uu____61574)
                                 in
                              (match uu____61511 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____61638 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____61638
                                      in
                                   let uu____61641 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____61641 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____61659 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____61659))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____61666 =
                                              let uu____61672 =
                                                let uu____61674 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____61676 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____61674 uu____61676
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____61672)
                                               in
                                            FStar_Errors.raise_error
                                              uu____61666
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
                                            let uu____61689 =
                                              let uu____61698 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____61715 =
                                                let uu____61724 =
                                                  let uu____61737 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____61737
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____61724
                                                 in
                                              FStar_List.append uu____61698
                                                uu____61715
                                               in
                                            let uu____61760 =
                                              let uu____61763 =
                                                let uu____61764 =
                                                  let uu____61769 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____61769
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____61764
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____61763
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____61689 uu____61760
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____61786 =
                                            let uu____61791 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____61792 =
                                              let uu____61793 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____61793 k4
                                               in
                                            (uu____61791, uu____61792)  in
                                          match uu____61786 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____61813 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____61813,
                                                (let uu___646_61819 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___646_61819.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___646_61819.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___646_61819.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___646_61819.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____61824 -> failwith "impossible"
  
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
            let uu____61888 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____61888 with
             | (usubst,_uvs1) ->
                 let uu____61911 =
                   let uu____61916 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____61917 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____61916, uu____61917)  in
                 (match uu____61911 with
                  | (env1,t1) ->
                      let uu____61924 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____61963  ->
                               match uu____61963 with
                               | (se1,u_tc) ->
                                   let uu____61978 =
                                     let uu____61980 =
                                       let uu____61981 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____61981  in
                                     FStar_Ident.lid_equals tc_lid
                                       uu____61980
                                      in
                                   if uu____61978
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____62001,uu____62002,tps,uu____62004,uu____62005,uu____62006)
                                          ->
                                          let tps1 =
                                            let uu____62016 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____62016
                                              (FStar_List.map
                                                 (fun uu____62056  ->
                                                    match uu____62056 with
                                                    | (x,uu____62070) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____62078 =
                                            let uu____62085 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____62085, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____62078
                                      | uu____62092 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____62135 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____62135
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____61924 with
                       | (env2,tps,u_tc) ->
                           let uu____62167 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____62183 =
                               let uu____62184 =
                                 FStar_Syntax_Subst.compress t2  in
                               uu____62184.FStar_Syntax_Syntax.n  in
                             match uu____62183 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____62223 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____62223 with
                                  | (uu____62264,bs') ->
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
                                                fun uu____62335  ->
                                                  match uu____62335 with
                                                  | (x,uu____62344) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____62351 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____62351)
                             | uu____62352 -> ([], t2)  in
                           (match uu____62167 with
                            | (arguments,result) ->
                                ((let uu____62396 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____62396
                                  then
                                    let uu____62399 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____62401 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____62404 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____62399 uu____62401 uu____62404
                                  else ());
                                 (let uu____62409 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____62409 with
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
                                      let uu____62427 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____62427 with
                                       | (result1,res_lcomp) ->
                                           let uu____62438 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____62438 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____62496 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____62496
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____62578  ->
                                                      fun uu____62579  ->
                                                        match (uu____62578,
                                                                uu____62579)
                                                        with
                                                        | ((bv,uu____62609),
                                                           (t2,uu____62611))
                                                            ->
                                                            let uu____62638 =
                                                              let uu____62639
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____62639.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____62638
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____62643 ->
                                                                 let uu____62644
                                                                   =
                                                                   let uu____62650
                                                                    =
                                                                    let uu____62652
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____62654
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____62652
                                                                    uu____62654
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____62650)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____62644
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____62659 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____62659
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____62661 =
                                                     let uu____62662 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____62662.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____62661 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____62665 -> ()
                                                   | uu____62666 ->
                                                       let uu____62667 =
                                                         let uu____62673 =
                                                           let uu____62675 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____62677 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____62675
                                                             uu____62677
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____62673)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____62667
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____62682 =
                                                       let uu____62683 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____62683.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____62682 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____62687;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____62688;_},tuvs)
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
                                                                    let uu____62702
                                                                    =
                                                                    let uu____62703
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____62704
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
                                                                    uu____62703
                                                                    uu____62704
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62702)
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
                                                     | uu____62710 ->
                                                         let uu____62711 =
                                                           let uu____62717 =
                                                             let uu____62719
                                                               =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____62721
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____62719
                                                               uu____62721
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____62717)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____62711
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____62739  ->
                                                            fun u_x  ->
                                                              match uu____62739
                                                              with
                                                              | (x,uu____62748)
                                                                  ->
                                                                  let uu____62753
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____62753)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____62757 =
                                                       let uu____62766 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun
                                                                 uu____62806 
                                                                 ->
                                                                 match uu____62806
                                                                 with
                                                                 | (x,uu____62820)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____62766
                                                         arguments1
                                                        in
                                                     let uu____62834 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____62757
                                                       uu____62834
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___768_62839 = se
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
                                                         (uu___768_62839.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___768_62839.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___768_62839.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___768_62839.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____62843 -> failwith "impossible"
  
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
            let uu___776_62910 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___776_62910.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___776_62910.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___776_62910.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____62920 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____62920
           then
             let uu____62925 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____62925
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____62968  ->
                     match uu____62968 with
                     | (se,uu____62974) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____62975,uu____62976,tps,k,uu____62979,uu____62980)
                              ->
                              let uu____62989 =
                                let uu____62990 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____62990
                                 in
                              FStar_Syntax_Syntax.null_binder uu____62989
                          | uu____62995 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____63024,uu____63025,t,uu____63027,uu____63028,uu____63029)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____63036 -> failwith "Impossible"))
              in
           let t =
             let uu____63041 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____63041
              in
           (let uu____63051 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____63051
            then
              let uu____63056 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____63056
            else ());
           (let uu____63061 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____63061 with
            | (uvs,t1) ->
                ((let uu____63081 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____63081
                  then
                    let uu____63086 =
                      let uu____63088 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____63088
                        (FStar_String.concat ", ")
                       in
                    let uu____63105 = FStar_Syntax_Print.term_to_string t1
                       in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____63086 uu____63105
                  else ());
                 (let uu____63110 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____63110 with
                  | (uvs1,t2) ->
                      let uu____63125 = FStar_Syntax_Util.arrow_formals t2
                         in
                      (match uu____63125 with
                       | (args,uu____63149) ->
                           let uu____63170 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____63170 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____63275  ->
                                       fun uu____63276  ->
                                         match (uu____63275, uu____63276)
                                         with
                                         | ((x,uu____63298),(se,uu____63300))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____63316,tps,uu____63318,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____63330 =
                                                    let uu____63335 =
                                                      let uu____63336 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____63336.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____63335 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____63365 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____63365
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____63443
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____63462 -> ([], ty)
                                                     in
                                                  (match uu____63330 with
                                                   | (tps1,t3) ->
                                                       let uu___853_63471 =
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
                                                           (uu___853_63471.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___853_63471.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___853_63471.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___853_63471.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____63476 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____63483 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _63487  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _63487))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___585_63506  ->
                                                match uu___585_63506 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____63512,uu____63513,uu____63514,uu____63515,uu____63516);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____63517;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____63518;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____63519;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____63520;_}
                                                    -> (tc, uvs_universes)
                                                | uu____63533 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____63557  ->
                                           fun d  ->
                                             match uu____63557 with
                                             | (t3,uu____63566) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____63572,uu____63573,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____63584 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____63584
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___889_63585 = d
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
                                                          (uu___889_63585.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___889_63585.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___889_63585.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___889_63585.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____63589 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____63608 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____63608
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____63630 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____63630
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____63647 =
      let uu____63648 = FStar_Syntax_Subst.compress t  in
      uu____63648.FStar_Syntax_Syntax.n  in
    match uu____63647 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____63667 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____63673 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____63710 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____63759  ->
               match uu____63759 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____63803 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____63803  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____63710
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____64008 =
             let uu____64010 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____64010
              in
           debug_log env uu____64008);
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
           (let uu____64015 =
              let uu____64017 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____64017
               in
            debug_log env uu____64015);
           (let uu____64022 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____64022) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____64035 =
                  let uu____64036 = FStar_Syntax_Subst.compress btype1  in
                  uu____64036.FStar_Syntax_Syntax.n  in
                match uu____64035 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____64066 = try_get_fv t  in
                    (match uu____64066 with
                     | (fv,us) ->
                         let uu____64074 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____64074
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____64090  ->
                                 match uu____64090 with
                                 | (t1,uu____64099) ->
                                     let uu____64104 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____64104) args)
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
                          let uu____64139 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____64139
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____64143 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____64143
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
                            (fun uu____64170  ->
                               match uu____64170 with
                               | (b,uu____64179) ->
                                   let uu____64184 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____64184) sbs)
                           &&
                           ((let uu____64190 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____64190 with
                             | (uu____64196,return_type) ->
                                 let uu____64198 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____64198)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____64199 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____64203 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____64208) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____64216) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____64223,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____64282  ->
                          match uu____64282 with
                          | (p,uu____64295,t) ->
                              let bs =
                                let uu____64314 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____64314
                                 in
                              let uu____64323 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____64323 with
                               | (bs1,t1) ->
                                   let uu____64331 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____64331)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____64333,uu____64334)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____64377 ->
                    ((let uu____64379 =
                        let uu____64381 =
                          let uu____64383 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____64385 =
                            let uu____64387 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____64387  in
                          Prims.op_Hat uu____64383 uu____64385  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____64381
                         in
                      debug_log env uu____64379);
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
              (let uu____64400 =
                 let uu____64402 =
                   let uu____64404 =
                     let uu____64406 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____64406  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____64404  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____64402
                  in
               debug_log env uu____64400);
              (let uu____64410 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____64410 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____64429 =
                       let uu____64431 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____64431
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____64429
                      then
                        ((let uu____64435 =
                            let uu____64437 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____64437
                             in
                          debug_log env uu____64435);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____64448 =
                        already_unfolded ilid args unfolded env  in
                      if uu____64448
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____64459 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____64459  in
                         (let uu____64465 =
                            let uu____64467 =
                              let uu____64469 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____64469
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____64467
                             in
                          debug_log env uu____64465);
                         (let uu____64474 =
                            let uu____64475 = FStar_ST.op_Bang unfolded  in
                            let uu____64501 =
                              let uu____64508 =
                                let uu____64513 =
                                  let uu____64514 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____64514  in
                                (ilid, uu____64513)  in
                              [uu____64508]  in
                            FStar_List.append uu____64475 uu____64501  in
                          FStar_ST.op_Colon_Equals unfolded uu____64474);
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
                  (let uu____64613 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____64613 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____64636 ->
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
                         (let uu____64640 =
                            let uu____64642 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____64642
                             in
                          debug_log env uu____64640);
                         (let uu____64645 =
                            let uu____64646 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____64646.FStar_Syntax_Syntax.n  in
                          match uu____64645 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____64674 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____64674 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____64738 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____64738 dbs1
                                       in
                                    let c1 =
                                      let uu____64742 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____64742 c
                                       in
                                    let uu____64745 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____64745 with
                                     | (args1,uu____64780) ->
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
                                           let uu____64872 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____64872 c1
                                            in
                                         ((let uu____64882 =
                                             let uu____64884 =
                                               let uu____64886 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____64889 =
                                                 let uu____64891 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____64891
                                                  in
                                               Prims.op_Hat uu____64886
                                                 uu____64889
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____64884
                                              in
                                           debug_log env uu____64882);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____64905 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____64908 =
                                  let uu____64909 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____64909.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____64908
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
                   (let uu____64948 = try_get_fv t1  in
                    match uu____64948 with
                    | (fv,uu____64955) ->
                        let uu____64956 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____64956
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____64988 =
                      let uu____64990 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____64990
                       in
                    debug_log env uu____64988);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____64995 =
                      FStar_List.fold_left
                        (fun uu____65016  ->
                           fun b  ->
                             match uu____65016 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____65047 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____65051 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____65047, uu____65051))) (true, env)
                        sbs1
                       in
                    match uu____64995 with | (b,uu____65069) -> b))
              | uu____65072 ->
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
              let uu____65108 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____65108 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____65131 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____65134 =
                      let uu____65136 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____65136
                       in
                    debug_log env uu____65134);
                   (let uu____65139 =
                      let uu____65140 = FStar_Syntax_Subst.compress dt  in
                      uu____65140.FStar_Syntax_Syntax.n  in
                    match uu____65139 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____65144 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____65149) ->
                        let dbs1 =
                          let uu____65179 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____65179  in
                        let dbs2 =
                          let uu____65229 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____65229 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____65234 =
                            let uu____65236 =
                              let uu____65238 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____65238 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____65236
                             in
                          debug_log env uu____65234);
                         (let uu____65248 =
                            FStar_List.fold_left
                              (fun uu____65269  ->
                                 fun b  ->
                                   match uu____65269 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____65300 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____65304 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____65300, uu____65304)))
                              (true, env) dbs3
                             in
                          match uu____65248 with | (b,uu____65322) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____65325,uu____65326) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____65362 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____65385 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____65401,uu____65402,uu____65403) -> (lid, us, bs)
        | uu____65412 -> failwith "Impossible!"  in
      match uu____65385 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____65424 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____65424 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____65448 =
                 let uu____65451 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____65451  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____65465 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____65465
                      unfolded_inductives env2) uu____65448)
  
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
        (uu____65500,uu____65501,t,uu____65503,uu____65504,uu____65505) -> t
    | uu____65512 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____65529 =
         let uu____65531 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____65531 haseq_suffix  in
       uu____65529 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____65541 =
      let uu____65544 =
        let uu____65547 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____65547]  in
      FStar_List.append lid.FStar_Ident.ns uu____65544  in
    FStar_Ident.lid_of_ids uu____65541
  
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
          let uu____65593 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____65607,bs,t,uu____65610,uu____65611) ->
                (lid, bs, t)
            | uu____65620 -> failwith "Impossible!"  in
          match uu____65593 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____65643 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____65643 t  in
              let uu____65652 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____65652 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____65670 =
                       let uu____65671 = FStar_Syntax_Subst.compress t2  in
                       uu____65671.FStar_Syntax_Syntax.n  in
                     match uu____65670 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____65675) -> ibs
                     | uu____65696 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____65705 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____65706 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____65705 uu____65706
                      in
                   let ind1 =
                     let uu____65712 =
                       let uu____65717 =
                         FStar_List.map
                           (fun uu____65734  ->
                              match uu____65734 with
                              | (bv,aq) ->
                                  let uu____65753 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65753, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____65717  in
                     uu____65712 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____65759 =
                       let uu____65764 =
                         FStar_List.map
                           (fun uu____65781  ->
                              match uu____65781 with
                              | (bv,aq) ->
                                  let uu____65800 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____65800, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____65764  in
                     uu____65759 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____65806 =
                       let uu____65811 =
                         let uu____65812 = FStar_Syntax_Syntax.as_arg ind2
                            in
                         [uu____65812]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____65811
                        in
                     uu____65806 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____65861 =
                            let uu____65862 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____65862  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____65861) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____65875 =
                              let uu____65878 =
                                let uu____65883 =
                                  let uu____65884 =
                                    let uu____65893 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____65893
                                     in
                                  [uu____65884]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____65883
                                 in
                              uu____65878 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____65875)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___1223_65916 = fml  in
                     let uu____65917 =
                       let uu____65918 =
                         let uu____65925 =
                           let uu____65926 =
                             let uu____65939 =
                               let uu____65950 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____65950]  in
                             [uu____65939]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____65926  in
                         (fml, uu____65925)  in
                       FStar_Syntax_Syntax.Tm_meta uu____65918  in
                     {
                       FStar_Syntax_Syntax.n = uu____65917;
                       FStar_Syntax_Syntax.pos =
                         (uu___1223_65916.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___1223_65916.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66003 =
                              let uu____66008 =
                                let uu____66009 =
                                  let uu____66018 =
                                    let uu____66019 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66019
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66018  in
                                [uu____66009]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66008
                               in
                            uu____66003 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____66072 =
                              let uu____66077 =
                                let uu____66078 =
                                  let uu____66087 =
                                    let uu____66088 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____66088
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____66087  in
                                [uu____66078]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____66077
                               in
                            uu____66072 FStar_Pervasives_Native.None
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
          let uu____66163 =
            let uu____66164 = FStar_Syntax_Subst.compress dt1  in
            uu____66164.FStar_Syntax_Syntax.n  in
          match uu____66163 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____66168) ->
              let dbs1 =
                let uu____66198 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____66198  in
              let dbs2 =
                let uu____66248 = FStar_Syntax_Subst.opening_of_binders bs
                   in
                FStar_Syntax_Subst.subst_binders uu____66248 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____66263 =
                           let uu____66268 =
                             let uu____66269 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____66269]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____66268
                            in
                         uu____66263 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____66300 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____66300 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____66308 =
                       let uu____66313 =
                         let uu____66314 =
                           let uu____66323 =
                             let uu____66324 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____66324
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____66323  in
                         [uu____66314]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____66313
                        in
                     uu____66308 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____66371 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____66462,uu____66463,uu____66464,uu____66465,uu____66466)
                  -> lid
              | uu____66475 -> failwith "Impossible!"  in
            let uu____66477 = acc  in
            match uu____66477 with
            | (uu____66514,en,uu____66516,uu____66517) ->
                let uu____66538 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____66538 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____66575 = acc  in
                     (match uu____66575 with
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
                                     (uu____66650,uu____66651,uu____66652,t_lid,uu____66654,uu____66655)
                                     -> t_lid = lid
                                 | uu____66662 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____66677 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____66677)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____66680 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____66683 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____66680, uu____66683)))
  
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
          let uu____66741 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____66751,us,uu____66753,t,uu____66755,uu____66756) ->
                (us, t)
            | uu____66765 -> failwith "Impossible!"  in
          match uu____66741 with
          | (us,t) ->
              let uu____66775 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____66775 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____66801 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____66801 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____66879 =
                             FStar_Syntax_Util.arrow_formals t  in
                           match uu____66879 with
                           | (uu____66894,t1) ->
                               let uu____66916 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____66916
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____66921 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____66921 with
                          | (phi1,uu____66929) ->
                              ((let uu____66931 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____66931
                                then
                                  let uu____66934 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____66934
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____66952  ->
                                         match uu____66952 with
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
                let uu____67024 =
                  let uu____67025 = FStar_Syntax_Subst.compress t  in
                  uu____67025.FStar_Syntax_Syntax.n  in
                match uu____67024 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____67033) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____67070 = is_mutual t'  in
                    if uu____67070
                    then true
                    else
                      (let uu____67077 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____67077)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____67097) ->
                    is_mutual t'
                | uu____67102 -> false
              
              and exists_mutual uu___586_67104 =
                match uu___586_67104 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____67125 =
                let uu____67126 = FStar_Syntax_Subst.compress dt1  in
                uu____67126.FStar_Syntax_Syntax.n  in
              match uu____67125 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____67132) ->
                  let dbs1 =
                    let uu____67162 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____67162  in
                  let dbs2 =
                    let uu____67212 =
                      FStar_Syntax_Subst.opening_of_binders bs  in
                    FStar_Syntax_Subst.subst_binders uu____67212 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____67232 =
                               let uu____67237 =
                                 let uu____67238 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____67238]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____67237
                                in
                             uu____67232 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____67268 = is_mutual sort  in
                             if uu____67268
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
                           let uu____67281 =
                             let uu____67286 =
                               let uu____67287 =
                                 let uu____67296 =
                                   let uu____67297 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____67297 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____67296  in
                               [uu____67287]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____67286
                              in
                           uu____67281 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____67344 -> acc
  
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
              let uu____67394 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____67416,bs,t,uu____67419,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____67431 -> failwith "Impossible!"  in
              match uu____67394 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____67455 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____67455 t  in
                  let uu____67464 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____67464 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____67474 =
                           let uu____67475 = FStar_Syntax_Subst.compress t2
                              in
                           uu____67475.FStar_Syntax_Syntax.n  in
                         match uu____67474 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____67479) ->
                             ibs
                         | uu____67500 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____67509 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____67510 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____67509
                           uu____67510
                          in
                       let ind1 =
                         let uu____67516 =
                           let uu____67521 =
                             FStar_List.map
                               (fun uu____67538  ->
                                  match uu____67538 with
                                  | (bv,aq) ->
                                      let uu____67557 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67557, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____67521  in
                         uu____67516 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____67563 =
                           let uu____67568 =
                             FStar_List.map
                               (fun uu____67585  ->
                                  match uu____67585 with
                                  | (bv,aq) ->
                                      let uu____67604 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____67604, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____67568  in
                         uu____67563 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____67610 =
                           let uu____67615 =
                             let uu____67616 =
                               FStar_Syntax_Syntax.as_arg ind2  in
                             [uu____67616]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____67615
                            in
                         uu____67610 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____67653,uu____67654,uu____67655,t_lid,uu____67657,uu____67658)
                                  -> t_lid = lid
                              | uu____67665 -> failwith "Impossible")
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
                         let uu___1460_67677 = fml  in
                         let uu____67678 =
                           let uu____67679 =
                             let uu____67686 =
                               let uu____67687 =
                                 let uu____67700 =
                                   let uu____67711 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____67711]  in
                                 [uu____67700]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____67687
                                in
                             (fml, uu____67686)  in
                           FStar_Syntax_Syntax.Tm_meta uu____67679  in
                         {
                           FStar_Syntax_Syntax.n = uu____67678;
                           FStar_Syntax_Syntax.pos =
                             (uu___1460_67677.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___1460_67677.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67764 =
                                  let uu____67769 =
                                    let uu____67770 =
                                      let uu____67779 =
                                        let uu____67780 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67780
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67779
                                       in
                                    [uu____67770]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67769
                                   in
                                uu____67764 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____67833 =
                                  let uu____67838 =
                                    let uu____67839 =
                                      let uu____67848 =
                                        let uu____67849 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____67849
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____67848
                                       in
                                    [uu____67839]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____67838
                                   in
                                uu____67833 FStar_Pervasives_Native.None
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
                     (lid,uu____67941,uu____67942,uu____67943,uu____67944,uu____67945)
                     -> lid
                 | uu____67954 -> failwith "Impossible!") tcs
             in
          let uu____67956 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____67968,uu____67969,uu____67970,uu____67971) ->
                (lid, us)
            | uu____67980 -> failwith "Impossible!"  in
          match uu____67956 with
          | (lid,us) ->
              let uu____67990 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____67990 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____68017 =
                       let uu____68018 =
                         let uu____68025 = get_haseq_axiom_lid lid  in
                         (uu____68025, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____68018  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____68017;
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
          let uu____68079 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___587_68104  ->
                    match uu___587_68104 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____68106;
                        FStar_Syntax_Syntax.sigrng = uu____68107;
                        FStar_Syntax_Syntax.sigquals = uu____68108;
                        FStar_Syntax_Syntax.sigmeta = uu____68109;
                        FStar_Syntax_Syntax.sigattrs = uu____68110;_} -> true
                    | uu____68132 -> false))
             in
          match uu____68079 with
          | (tys,datas) ->
              ((let uu____68155 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___588_68166  ->
                          match uu___588_68166 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____68168;
                              FStar_Syntax_Syntax.sigrng = uu____68169;
                              FStar_Syntax_Syntax.sigquals = uu____68170;
                              FStar_Syntax_Syntax.sigmeta = uu____68171;
                              FStar_Syntax_Syntax.sigattrs = uu____68172;_}
                              -> false
                          | uu____68193 -> true))
                   in
                if uu____68155
                then
                  let uu____68196 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____68196
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____68211 =
                       let uu____68212 = FStar_List.hd tys  in
                       uu____68212.FStar_Syntax_Syntax.sigel  in
                     match uu____68211 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____68215,uvs,uu____68217,uu____68218,uu____68219,uu____68220)
                         -> uvs
                     | uu____68229 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____68234 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____68264 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____68264 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____68302,bs,t,l1,l2) ->
                                      let uu____68315 =
                                        let uu____68332 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____68333 =
                                          let uu____68334 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst
                                            uu____68334 t
                                           in
                                        (lid, univs2, uu____68332,
                                          uu____68333, l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____68315
                                  | uu____68347 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1556_68349 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1556_68349.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1556_68349.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1556_68349.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1556_68349.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____68359,t,lid_t,x,l) ->
                                      let uu____68370 =
                                        let uu____68386 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____68386, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____68370
                                  | uu____68390 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___1570_68392 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___1570_68392.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___1570_68392.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___1570_68392.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___1570_68392.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____68393 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____68393, tys1, datas1))
                   in
                match uu____68234 with
                | (env1,tys1,datas1) ->
                    let uu____68419 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____68458  ->
                             match uu____68458 with
                             | (env2,all_tcs,g) ->
                                 let uu____68498 = tc_tycon env2 tc  in
                                 (match uu____68498 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____68525 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____68525
                                        then
                                          let uu____68528 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____68528
                                        else ());
                                       (let uu____68533 =
                                          let uu____68534 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____68534
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____68533))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____68419 with
                     | (env2,tcs,g) ->
                         let uu____68580 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____68602  ->
                                  match uu____68602 with
                                  | (datas2,g1) ->
                                      let uu____68621 =
                                        let uu____68626 = tc_data env2 tcs
                                           in
                                        uu____68626 se  in
                                      (match uu____68621 with
                                       | (data,g') ->
                                           let uu____68643 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____68643)))
                             datas1 ([], g)
                            in
                         (match uu____68580 with
                          | (datas2,g1) ->
                              let uu____68664 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____68686 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____68686, datas2))
                                 in
                              (match uu____68664 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____68718 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____68719 =
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
                                         uu____68718;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____68719
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____68745,uu____68746)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____68766 =
                                                    let uu____68772 =
                                                      let uu____68774 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____68776 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____68774
                                                        uu____68776
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____68772)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____68766
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____68780 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____68780 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____68796)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____68827 ->
                                                             let uu____68828
                                                               =
                                                               let uu____68835
                                                                 =
                                                                 let uu____68836
                                                                   =
                                                                   let uu____68851
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____68851)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____68836
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____68835
                                                                in
                                                             uu____68828
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
                                                       let uu____68873 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____68873
                                                        with
                                                        | (uu____68878,inferred)
                                                            ->
                                                            let uu____68880 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____68880
                                                             with
                                                             | (uu____68885,expected)
                                                                 ->
                                                                 let uu____68887
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____68887
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____68894 -> ()));
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
                          let uu____69005 =
                            let uu____69012 =
                              let uu____69013 =
                                let uu____69020 =
                                  let uu____69023 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____69023
                                   in
                                (uu____69020, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____69013  in
                            FStar_Syntax_Syntax.mk uu____69012  in
                          uu____69005 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____69057  ->
                                  match uu____69057 with
                                  | (x,imp) ->
                                      let uu____69076 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____69076, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____69080 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____69080  in
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
                               let uu____69103 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____69103
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____69105 =
                               let uu____69108 =
                                 let uu____69111 =
                                   let uu____69116 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____69117 =
                                     let uu____69118 =
                                       let uu____69127 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____69127
                                        in
                                     [uu____69118]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____69116
                                     uu____69117
                                    in
                                 uu____69111 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____69108  in
                             FStar_Syntax_Util.refine x uu____69105  in
                           let uu____69152 =
                             let uu___1671_69153 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1671_69153.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1671_69153.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____69152)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____69170 =
                          FStar_List.map
                            (fun uu____69194  ->
                               match uu____69194 with
                               | (x,uu____69208) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____69170 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____69267  ->
                                match uu____69267 with
                                | (x,uu____69281) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____69292 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____69292)
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
                               (let uu____69313 =
                                  let uu____69315 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____69315.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____69313)
                              in
                           let quals =
                             let uu____69319 =
                               FStar_List.filter
                                 (fun uu___589_69323  ->
                                    match uu___589_69323 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____69328 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____69319
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____69366 =
                                 let uu____69367 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____69367  in
                               FStar_Syntax_Syntax.mk_Total uu____69366  in
                             let uu____69368 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____69368
                              in
                           let decl =
                             let uu____69372 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____69372;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____69374 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____69374
                            then
                              let uu____69378 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____69378
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
                                             fun uu____69439  ->
                                               match uu____69439 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____69464 =
                                                       let uu____69467 =
                                                         let uu____69468 =
                                                           let uu____69475 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____69475,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____69468
                                                          in
                                                       pos uu____69467  in
                                                     (uu____69464, b)
                                                   else
                                                     (let uu____69483 =
                                                        let uu____69486 =
                                                          let uu____69487 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____69487
                                                           in
                                                        pos uu____69486  in
                                                      (uu____69483, b))))
                                      in
                                   let pat_true =
                                     let uu____69506 =
                                       let uu____69509 =
                                         let uu____69510 =
                                           let uu____69524 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____69524, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____69510
                                          in
                                       pos uu____69509  in
                                     (uu____69506,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____69559 =
                                       let uu____69562 =
                                         let uu____69563 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____69563
                                          in
                                       pos uu____69562  in
                                     (uu____69559,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____69577 =
                                     let uu____69584 =
                                       let uu____69585 =
                                         let uu____69608 =
                                           let uu____69625 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____69640 =
                                             let uu____69657 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____69657]  in
                                           uu____69625 :: uu____69640  in
                                         (arg_exp, uu____69608)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____69585
                                        in
                                     FStar_Syntax_Syntax.mk uu____69584  in
                                   uu____69577 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____69733 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____69733
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
                                let uu____69755 =
                                  let uu____69760 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____69760  in
                                let uu____69761 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____69755
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____69761 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____69767 =
                                  let uu____69768 =
                                    let uu____69775 =
                                      let uu____69778 =
                                        let uu____69779 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____69779
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____69778]  in
                                    ((false, [lb]), uu____69775)  in
                                  FStar_Syntax_Syntax.Sig_let uu____69768  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____69767;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____69793 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____69793
                               then
                                 let uu____69797 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____69797
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
                                fun uu____69870  ->
                                  match uu____69870 with
                                  | (a,uu____69879) ->
                                      let uu____69884 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____69884 with
                                       | (field_name,uu____69890) ->
                                           let field_proj_tm =
                                             let uu____69892 =
                                               let uu____69893 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____69893
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____69892 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____69919 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____69961  ->
                                    match uu____69961 with
                                    | (x,uu____69972) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____69978 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____69978 with
                                         | (field_name,uu____69986) ->
                                             let t =
                                               let uu____69990 =
                                                 let uu____69991 =
                                                   let uu____69994 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____69994
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____69991
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____69990
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____70000 =
                                                    let uu____70002 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____70002.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____70000)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____70021 =
                                                   FStar_List.filter
                                                     (fun uu___590_70025  ->
                                                        match uu___590_70025
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____70028 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____70021
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___591_70043  ->
                                                         match uu___591_70043
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____70049 ->
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
                                               let uu____70060 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____70060;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____70062 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____70062
                                               then
                                                 let uu____70066 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____70066
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
                                                           fun uu____70120 
                                                             ->
                                                             match uu____70120
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
                                                                   let uu____70146
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____70146,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____70162
                                                                    =
                                                                    let uu____70165
                                                                    =
                                                                    let uu____70166
                                                                    =
                                                                    let uu____70173
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____70173,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____70166
                                                                     in
                                                                    pos
                                                                    uu____70165
                                                                     in
                                                                    (uu____70162,
                                                                    b))
                                                                   else
                                                                    (let uu____70181
                                                                    =
                                                                    let uu____70184
                                                                    =
                                                                    let uu____70185
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____70185
                                                                     in
                                                                    pos
                                                                    uu____70184
                                                                     in
                                                                    (uu____70181,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____70204 =
                                                     let uu____70207 =
                                                       let uu____70208 =
                                                         let uu____70222 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____70222,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____70208
                                                        in
                                                     pos uu____70207  in
                                                   let uu____70232 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____70204,
                                                     FStar_Pervasives_Native.None,
                                                     uu____70232)
                                                    in
                                                 let body =
                                                   let uu____70248 =
                                                     let uu____70255 =
                                                       let uu____70256 =
                                                         let uu____70279 =
                                                           let uu____70296 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____70296]  in
                                                         (arg_exp,
                                                           uu____70279)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____70256
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____70255
                                                      in
                                                   uu____70248
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____70361 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____70361
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
                                                   let uu____70380 =
                                                     let uu____70385 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____70385
                                                      in
                                                   let uu____70386 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____70380;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____70386;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____70392 =
                                                     let uu____70393 =
                                                       let uu____70400 =
                                                         let uu____70403 =
                                                           let uu____70404 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____70404
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____70403]  in
                                                       ((false, [lb]),
                                                         uu____70400)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____70393
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____70392;
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
                                                 (let uu____70418 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____70418
                                                  then
                                                    let uu____70422 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____70422
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____69919 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____70476) when
              let uu____70483 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____70483 ->
              let uu____70485 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____70485 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____70507 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____70507 with
                    | (formals,uu____70525) ->
                        let uu____70546 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____70581 =
                                   let uu____70583 =
                                     let uu____70584 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____70584  in
                                   FStar_Ident.lid_equals typ_lid uu____70583
                                    in
                                 if uu____70581
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____70606,uvs',tps,typ0,uu____70610,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____70630 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____70679 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____70679
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____70546 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____70717 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____70717 with
                              | (indices,uu____70735) ->
                                  let refine_domain =
                                    let uu____70758 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___592_70765  ->
                                              match uu___592_70765 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____70767 -> true
                                              | uu____70777 -> false))
                                       in
                                    if uu____70758
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___593_70792 =
                                      match uu___593_70792 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____70795,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____70807 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____70808 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____70808 with
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
                                    let uu____70821 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____70821 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____70904  ->
                                               fun uu____70905  ->
                                                 match (uu____70904,
                                                         uu____70905)
                                                 with
                                                 | ((x,uu____70931),(x',uu____70933))
                                                     ->
                                                     let uu____70954 =
                                                       let uu____70961 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____70961)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____70954) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____70966 -> []
  