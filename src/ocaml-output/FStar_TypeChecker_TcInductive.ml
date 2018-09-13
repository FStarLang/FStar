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
      (FStar_TypeChecker_Env.env_t,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe,
        FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ (tc,uvs,tps,k,mutuals,data) ->
          let env0 = env  in
          let uu____50 = FStar_Syntax_Subst.univ_var_opening uvs  in
          (match uu____50 with
           | (usubst,uvs1) ->
               let uu____77 =
                 let uu____84 = FStar_TypeChecker_Env.push_univ_vars env uvs1
                    in
                 let uu____85 = FStar_Syntax_Subst.subst_binders usubst tps
                    in
                 let uu____86 =
                   let uu____87 =
                     FStar_Syntax_Subst.shift_subst (FStar_List.length tps)
                       usubst
                      in
                   FStar_Syntax_Subst.subst uu____87 k  in
                 (uu____84, uu____85, uu____86)  in
               (match uu____77 with
                | (env1,tps1,k1) ->
                    let uu____107 = FStar_Syntax_Subst.open_term tps1 k1  in
                    (match uu____107 with
                     | (tps2,k2) ->
                         let uu____122 =
                           FStar_TypeChecker_TcTerm.tc_binders env1 tps2  in
                         (match uu____122 with
                          | (tps3,env_tps,guard_params,us) ->
                              let uu____143 =
                                let uu____162 =
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    env_tps k2
                                   in
                                match uu____162 with
                                | (k3,uu____188,g) ->
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
                                    let uu____191 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____206 =
                                      let uu____207 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____207
                                       in
                                    (uu____191, uu____206)
                                 in
                              (match uu____143 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____270 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____270
                                      in
                                   let uu____273 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____273 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____290 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____290))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____294 =
                                              let uu____299 =
                                                let uu____300 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____301 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____300 uu____301
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____299)
                                               in
                                            FStar_Errors.raise_error
                                              uu____294
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
                                            let uu____310 =
                                              let uu____319 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____336 =
                                                let uu____345 =
                                                  let uu____358 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____358
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____345
                                                 in
                                              FStar_List.append uu____319
                                                uu____336
                                               in
                                            let uu____381 =
                                              let uu____384 =
                                                let uu____385 =
                                                  let uu____390 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____390
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____385
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____384
                                               in
                                            FStar_Syntax_Util.arrow uu____310
                                              uu____381
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____407 =
                                            let uu____412 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____413 =
                                              let uu____414 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____414 k4
                                               in
                                            (uu____412, uu____413)  in
                                          match uu____407 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____434 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____434,
                                                (let uu___357_440 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___357_440.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___357_440.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___357_440.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___357_440.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____445 -> failwith "impossible"
  
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun tcs  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (c,_uvs,t,tc_lid,ntps,_mutual_tcs)
            ->
            let uu____505 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____505 with
             | (usubst,_uvs1) ->
                 let uu____528 =
                   let uu____533 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____534 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____533, uu____534)  in
                 (match uu____528 with
                  | (env1,t1) ->
                      let uu____541 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____580  ->
                               match uu____580 with
                               | (se1,u_tc) ->
                                   let uu____595 =
                                     let uu____596 =
                                       let uu____597 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____597  in
                                     FStar_Ident.lid_equals tc_lid uu____596
                                      in
                                   if uu____595
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____616,uu____617,tps,uu____619,uu____620,uu____621)
                                          ->
                                          let tps1 =
                                            let uu____631 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____631
                                              (FStar_List.map
                                                 (fun uu____671  ->
                                                    match uu____671 with
                                                    | (x,uu____685) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____693 =
                                            let uu____700 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____700, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____693
                                      | uu____707 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____748 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____748
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____541 with
                       | (env2,tps,u_tc) ->
                           let uu____775 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____791 =
                               let uu____792 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____792.FStar_Syntax_Syntax.n  in
                             match uu____791 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____831 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____831 with
                                  | (uu____872,bs') ->
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
                                                fun uu____943  ->
                                                  match uu____943 with
                                                  | (x,uu____951) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____956 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____956)
                             | uu____957 -> ([], t2)  in
                           (match uu____775 with
                            | (arguments,result) ->
                                ((let uu____1001 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____1001
                                  then
                                    let uu____1002 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____1003 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____1004 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1002 uu____1003 uu____1004
                                  else ());
                                 (let uu____1006 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____1006 with
                                  | (arguments1,env',us) ->
                                      let uu____1020 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____1020 with
                                       | (result1,res_lcomp) ->
                                           let ty =
                                             let uu____1032 =
                                               unfold_whnf env2
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ
                                                in
                                             FStar_All.pipe_right uu____1032
                                               FStar_Syntax_Util.unrefine
                                              in
                                           ((let uu____1034 =
                                               let uu____1035 =
                                                 FStar_Syntax_Subst.compress
                                                   ty
                                                  in
                                               uu____1035.FStar_Syntax_Syntax.n
                                                in
                                             match uu____1034 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____1038 -> ()
                                             | uu____1039 ->
                                                 let uu____1040 =
                                                   let uu____1045 =
                                                     let uu____1046 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____1047 =
                                                       FStar_Syntax_Print.term_to_string
                                                         ty
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____1046 uu____1047
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____1045)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____1040
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____1048 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____1048 with
                                             | (head1,uu____1070) ->
                                                 let g_uvs =
                                                   let uu____1096 =
                                                     let uu____1097 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____1097.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1096 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____1101;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____1102;_},tuvs)
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
                                                                  let uu____1115
                                                                    =
                                                                    let uu____1116
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1117
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    (FStar_Syntax_Syntax.U_name
                                                                    u2))
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env'
                                                                    uu____1116
                                                                    uu____1117
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1115)
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
                                                   | uu____1120 ->
                                                       let uu____1121 =
                                                         let uu____1126 =
                                                           let uu____1127 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____1128 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____1127
                                                             uu____1128
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____1126)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1121
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____1143  ->
                                                          fun u_x  ->
                                                            match uu____1143
                                                            with
                                                            | (x,uu____1152)
                                                                ->
                                                                let uu____1157
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g
                                                                  uu____1157)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____1161 =
                                                     let uu____1170 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1210 
                                                               ->
                                                               match uu____1210
                                                               with
                                                               | (x,uu____1224)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____1170 arguments1
                                                      in
                                                   let uu____1237 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1161 uu____1237
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___358_1242 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___358_1242.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___358_1242.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___358_1242.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___358_1242.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1245 -> failwith "impossible"
  
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    FStar_TypeChecker_Env.guard_t ->
      (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universe)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          (FStar_Syntax_Syntax.sigelt Prims.list,FStar_Syntax_Syntax.sigelt
                                                   Prims.list)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun tcs  ->
        fun datas  ->
          let tc_universe_vars =
            FStar_List.map FStar_Pervasives_Native.snd tcs  in
          let g1 =
            let uu___359_1310 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___359_1310.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___359_1310.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___359_1310.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1320 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1320
           then
             let uu____1321 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1321
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1361  ->
                     match uu____1361 with
                     | (se,uu____1367) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1368,uu____1369,tps,k,uu____1372,uu____1373)
                              ->
                              let uu____1382 =
                                let uu____1383 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1383
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1382
                          | uu____1388 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1416,uu____1417,t,uu____1419,uu____1420,uu____1421)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1426 -> failwith "Impossible"))
              in
           let t =
             let uu____1430 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1430
              in
           (let uu____1440 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1440
            then
              let uu____1441 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1441
            else ());
           (let uu____1443 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1443 with
            | (uvs,t1) ->
                ((let uu____1463 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1463
                  then
                    let uu____1464 =
                      let uu____1465 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1465
                        (FStar_String.concat ", ")
                       in
                    let uu____1476 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1464 uu____1476
                  else ());
                 (let uu____1478 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1478 with
                  | (uvs1,t2) ->
                      let uu____1493 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1493 with
                       | (args,uu____1517) ->
                           let uu____1538 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1538 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1643  ->
                                       fun uu____1644  ->
                                         match (uu____1643, uu____1644) with
                                         | ((x,uu____1666),(se,uu____1668))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1684,tps,uu____1686,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1698 =
                                                    let uu____1703 =
                                                      let uu____1704 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1704.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1703 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1733 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1733
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1811
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1830 -> ([], ty)
                                                     in
                                                  (match uu____1698 with
                                                   | (tps1,t3) ->
                                                       let uu___360_1839 = se
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
                                                           (uu___360_1839.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___360_1839.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___360_1839.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___360_1839.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1844 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1850 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _0_16  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _0_16))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___348_1872  ->
                                                match uu___348_1872 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1878,uu____1879,uu____1880,uu____1881,uu____1882);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1883;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1884;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1885;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1886;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1899 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1922  ->
                                           fun d  ->
                                             match uu____1922 with
                                             | (t3,uu____1931) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1937,uu____1938,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1947 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1947
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___361_1948 = d
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
                                                          (uu___361_1948.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___361_1948.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___361_1948.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___361_1948.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1951 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____1966 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1966
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1978 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1978
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1994 =
      let uu____1995 = FStar_Syntax_Subst.compress t  in
      uu____1995.FStar_Syntax_Syntax.n  in
    match uu____1994 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2014 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2019 -> failwith "Node is not an fvar or a Tm_uinst"
  
type unfolded_memo_elt =
  (FStar_Ident.lident,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple2 Prims.list
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
          let uu____2072 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2141  ->
               match uu____2141 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2184 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2184  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2072
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2428 =
             let uu____2429 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2429
              in
           debug_log env uu____2428);
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
           (let uu____2432 =
              let uu____2433 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2433
               in
            debug_log env uu____2432);
           (let uu____2436 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2436) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2447 =
                  let uu____2448 = FStar_Syntax_Subst.compress btype1  in
                  uu____2448.FStar_Syntax_Syntax.n  in
                match uu____2447 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2477 = try_get_fv t  in
                    (match uu____2477 with
                     | (fv,us) ->
                         let uu____2484 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2484
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2496  ->
                                 match uu____2496 with
                                 | (t1,uu____2504) ->
                                     let uu____2509 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2509) args)
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
                          let uu____2559 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2559
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2563 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2563
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
                            (fun uu____2583  ->
                               match uu____2583 with
                               | (b,uu____2591) ->
                                   let uu____2596 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2596) sbs)
                           &&
                           ((let uu____2601 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2601 with
                             | (uu____2606,return_type) ->
                                 let uu____2608 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2608)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2629 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2631 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2634) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2661) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2687,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2745  ->
                          match uu____2745 with
                          | (p,uu____2757,t) ->
                              let bs =
                                let uu____2776 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2776
                                 in
                              let uu____2785 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2785 with
                               | (bs1,t1) ->
                                   let uu____2792 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2792)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2814,uu____2815)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2877 ->
                    ((let uu____2879 =
                        let uu____2880 =
                          let uu____2881 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2882 =
                            let uu____2883 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2883  in
                          Prims.strcat uu____2881 uu____2882  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2880
                         in
                      debug_log env uu____2879);
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
              (let uu____2901 =
                 let uu____2902 =
                   let uu____2903 =
                     let uu____2904 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2904  in
                   Prims.strcat ilid.FStar_Ident.str uu____2903  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2902
                  in
               debug_log env uu____2901);
              (let uu____2905 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2905 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____2918 =
                       let uu____2919 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____2919
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____2918
                      then
                        ((let uu____2921 =
                            let uu____2922 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____2922
                             in
                          debug_log env uu____2921);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____2926 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2926
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____2950 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____2950  in
                         (let uu____2954 =
                            let uu____2955 =
                              let uu____2956 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2956
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2955
                             in
                          debug_log env uu____2954);
                         (let uu____2958 =
                            let uu____2959 = FStar_ST.op_Bang unfolded  in
                            let uu____3005 =
                              let uu____3012 =
                                let uu____3017 =
                                  let uu____3018 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3018  in
                                (ilid, uu____3017)  in
                              [uu____3012]  in
                            FStar_List.append uu____2959 uu____3005  in
                          FStar_ST.op_Colon_Equals unfolded uu____2958);
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
                    (Prims.strcat
                       "Checking nested positivity in data constructor "
                       (Prims.strcat dlid.FStar_Ident.str
                          (Prims.strcat " of the inductive "
                             ilid.FStar_Ident.str)));
                  (let uu____3163 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3163 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3185 ->
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
                         (let uu____3188 =
                            let uu____3189 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3189
                             in
                          debug_log env uu____3188);
                         (let uu____3190 =
                            let uu____3191 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3191.FStar_Syntax_Syntax.n  in
                          match uu____3190 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3217 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3217 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3280 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3280 dbs1
                                       in
                                    let c1 =
                                      let uu____3284 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3284 c
                                       in
                                    let uu____3287 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3287 with
                                     | (args1,uu____3321) ->
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
                                           let uu____3413 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3413 c1
                                            in
                                         ((let uu____3423 =
                                             let uu____3424 =
                                               let uu____3425 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3426 =
                                                 let uu____3427 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3427
                                                  in
                                               Prims.strcat uu____3425
                                                 uu____3426
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3424
                                              in
                                           debug_log env uu____3423);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3458 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3460 =
                                  let uu____3461 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3461.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3460
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
                   (let uu____3527 = try_get_fv t1  in
                    match uu____3527 with
                    | (fv,uu____3533) ->
                        let uu____3534 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3534
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3559 =
                      let uu____3560 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3560
                       in
                    debug_log env uu____3559);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3562 =
                      FStar_List.fold_left
                        (fun uu____3581  ->
                           fun b  ->
                             match uu____3581 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3604 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3627 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3604, uu____3627))) (true, env)
                        sbs1
                       in
                    match uu____3562 with | (b,uu____3641) -> b))
              | uu____3642 ->
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
              let uu____3693 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3693 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3715 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3717 =
                      let uu____3718 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3718
                       in
                    debug_log env uu____3717);
                   (let uu____3719 =
                      let uu____3720 = FStar_Syntax_Subst.compress dt  in
                      uu____3720.FStar_Syntax_Syntax.n  in
                    match uu____3719 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3723 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3726) ->
                        let dbs1 =
                          let uu____3756 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3756  in
                        let dbs2 =
                          let uu____3806 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3806 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3811 =
                            let uu____3812 =
                              let uu____3813 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3813 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3812
                             in
                          debug_log env uu____3811);
                         (let uu____3820 =
                            FStar_List.fold_left
                              (fun uu____3839  ->
                                 fun b  ->
                                   match uu____3839 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3862 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3885 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3862, uu____3885)))
                              (true, env) dbs3
                             in
                          match uu____3820 with | (b,uu____3899) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3900,uu____3901) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3954 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3972 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3988,uu____3989,uu____3990) -> (lid, us, bs)
        | uu____3999 -> failwith "Impossible!"  in
      match uu____3972 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4009 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4009 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4032 =
                 let uu____4035 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4035  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4047 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4047
                      unfolded_inductives env2) uu____4032)
  
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
        (uu____4122,uu____4123,t,uu____4125,uu____4126,uu____4127) -> t
    | uu____4132 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4152 =
         let uu____4153 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4153 haseq_suffix  in
       uu____4152 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4173 =
      let uu____4176 =
        let uu____4179 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4179]  in
      FStar_List.append lid.FStar_Ident.ns uu____4176  in
    FStar_Ident.lid_of_ids uu____4173
  
let (get_optimized_haseq_axiom :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Syntax_Syntax.subst_elt Prims.list ->
        FStar_Syntax_Syntax.univ_names ->
          (FStar_Ident.lident,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders,
            FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple5)
  =
  fun en  ->
    fun ty  ->
      fun usubst  ->
        fun us  ->
          let uu____4224 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4238,bs,t,uu____4241,uu____4242) -> (lid, bs, t)
            | uu____4251 -> failwith "Impossible!"  in
          match uu____4224 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4273 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4273 t  in
              let uu____4282 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4282 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4300 =
                       let uu____4301 = FStar_Syntax_Subst.compress t2  in
                       uu____4301.FStar_Syntax_Syntax.n  in
                     match uu____4300 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4305) -> ibs
                     | uu____4326 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4335 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4336 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4335 uu____4336
                      in
                   let ind1 =
                     let uu____4342 =
                       let uu____4347 =
                         FStar_List.map
                           (fun uu____4364  ->
                              match uu____4364 with
                              | (bv,aq) ->
                                  let uu____4383 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4383, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4347  in
                     uu____4342 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4391 =
                       let uu____4396 =
                         FStar_List.map
                           (fun uu____4413  ->
                              match uu____4413 with
                              | (bv,aq) ->
                                  let uu____4432 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4432, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4396  in
                     uu____4391 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4440 =
                       let uu____4445 =
                         let uu____4446 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4446]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4445
                        in
                     uu____4440 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4497 =
                            let uu____4498 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4498  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4497) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4511 =
                              let uu____4514 =
                                let uu____4519 =
                                  let uu____4520 =
                                    let uu____4529 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4529  in
                                  [uu____4520]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4519
                                 in
                              uu____4514 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4511)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___362_4554 = fml  in
                     let uu____4555 =
                       let uu____4556 =
                         let uu____4563 =
                           let uu____4564 =
                             let uu____4577 =
                               let uu____4588 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4588]  in
                             [uu____4577]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4564  in
                         (fml, uu____4563)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4556  in
                     {
                       FStar_Syntax_Syntax.n = uu____4555;
                       FStar_Syntax_Syntax.pos =
                         (uu___362_4554.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___362_4554.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4643 =
                              let uu____4648 =
                                let uu____4649 =
                                  let uu____4658 =
                                    let uu____4659 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4659 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4658  in
                                [uu____4649]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4648
                               in
                            uu____4643 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4716 =
                              let uu____4721 =
                                let uu____4722 =
                                  let uu____4731 =
                                    let uu____4732 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4732 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4731  in
                                [uu____4722]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4721
                               in
                            uu____4716 FStar_Pervasives_Native.None
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
          let uu____4808 =
            let uu____4809 = FStar_Syntax_Subst.compress dt1  in
            uu____4809.FStar_Syntax_Syntax.n  in
          match uu____4808 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4813) ->
              let dbs1 =
                let uu____4843 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4843  in
              let dbs2 =
                let uu____4893 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4893 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4908 =
                           let uu____4913 =
                             let uu____4914 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4914]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4913
                            in
                         uu____4908 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4947 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4947 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4955 =
                       let uu____4960 =
                         let uu____4961 =
                           let uu____4970 =
                             let uu____4971 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4971
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4970  in
                         [uu____4961]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4960
                        in
                     uu____4955 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5020 -> FStar_Syntax_Util.t_true
  
let (optimized_haseq_ty :
  FStar_Syntax_Syntax.sigelts ->
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple4 ->
          FStar_Syntax_Syntax.sigelt ->
            ((FStar_Ident.lident,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple2 Prims.list,FStar_TypeChecker_Env.env,
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                                    FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple4)
  =
  fun all_datas_in_the_bundle  ->
    fun usubst  ->
      fun us  ->
        fun acc  ->
          fun ty  ->
            let lid =
              match ty.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ
                  (lid,uu____5110,uu____5111,uu____5112,uu____5113,uu____5114)
                  -> lid
              | uu____5123 -> failwith "Impossible!"  in
            let uu____5124 = acc  in
            match uu____5124 with
            | (uu____5161,en,uu____5163,uu____5164) ->
                let uu____5185 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5185 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5222 = acc  in
                     (match uu____5222 with
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
                                     (uu____5296,uu____5297,uu____5298,t_lid,uu____5300,uu____5301)
                                     -> t_lid = lid
                                 | uu____5306 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5319 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5319)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5322 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5325 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5322, uu____5325)))
  
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
          let uu____5382 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5392,us,uu____5394,t,uu____5396,uu____5397) -> 
                (us, t)
            | uu____5406 -> failwith "Impossible!"  in
          match uu____5382 with
          | (us,t) ->
              let uu____5415 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5415 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5440 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5440 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5518 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5518 with
                           | (uu____5533,t1) ->
                               let uu____5555 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5555
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5557 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5557 with
                          | (phi1,uu____5565) ->
                              ((let uu____5567 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5567
                                then
                                  let uu____5568 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5568
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5585  ->
                                         match uu____5585 with
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
                let uu____5653 =
                  let uu____5654 = FStar_Syntax_Subst.compress t  in
                  uu____5654.FStar_Syntax_Syntax.n  in
                match uu____5653 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5661) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5698 = is_mutual t'  in
                    if uu____5698
                    then true
                    else
                      (let uu____5700 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5700)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5720) -> is_mutual t'
                | uu____5725 -> false
              
              and exists_mutual uu___349_5726 =
                match uu___349_5726 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5745 =
                let uu____5746 = FStar_Syntax_Subst.compress dt1  in
                uu____5746.FStar_Syntax_Syntax.n  in
              match uu____5745 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5752) ->
                  let dbs1 =
                    let uu____5782 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5782  in
                  let dbs2 =
                    let uu____5832 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5832 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5852 =
                               let uu____5857 =
                                 let uu____5858 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5858]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5857
                                in
                             uu____5852 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5890 = is_mutual sort  in
                             if uu____5890
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
                           let uu____5902 =
                             let uu____5907 =
                               let uu____5908 =
                                 let uu____5917 =
                                   let uu____5918 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5918 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5917  in
                               [uu____5908]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5907
                              in
                           uu____5902 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5967 -> acc
  
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
              let uu____6016 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6038,bs,t,uu____6041,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6053 -> failwith "Impossible!"  in
              match uu____6016 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6076 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6076 t  in
                  let uu____6085 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6085 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6095 =
                           let uu____6096 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6096.FStar_Syntax_Syntax.n  in
                         match uu____6095 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6100) ->
                             ibs
                         | uu____6121 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6130 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6131 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6130
                           uu____6131
                          in
                       let ind1 =
                         let uu____6137 =
                           let uu____6142 =
                             FStar_List.map
                               (fun uu____6159  ->
                                  match uu____6159 with
                                  | (bv,aq) ->
                                      let uu____6178 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6178, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6142  in
                         uu____6137 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6186 =
                           let uu____6191 =
                             FStar_List.map
                               (fun uu____6208  ->
                                  match uu____6208 with
                                  | (bv,aq) ->
                                      let uu____6227 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6227, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6191  in
                         uu____6186 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6235 =
                           let uu____6240 =
                             let uu____6241 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6241]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6240
                            in
                         uu____6235 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6279,uu____6280,uu____6281,t_lid,uu____6283,uu____6284)
                                  -> t_lid = lid
                              | uu____6289 -> failwith "Impossible")
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
                         let uu___363_6299 = fml  in
                         let uu____6300 =
                           let uu____6301 =
                             let uu____6308 =
                               let uu____6309 =
                                 let uu____6322 =
                                   let uu____6333 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____6333]  in
                                 [uu____6322]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6309
                                in
                             (fml, uu____6308)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6301  in
                         {
                           FStar_Syntax_Syntax.n = uu____6300;
                           FStar_Syntax_Syntax.pos =
                             (uu___363_6299.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___363_6299.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6388 =
                                  let uu____6393 =
                                    let uu____6394 =
                                      let uu____6403 =
                                        let uu____6404 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6404
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6403
                                       in
                                    [uu____6394]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6393
                                   in
                                uu____6388 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6461 =
                                  let uu____6466 =
                                    let uu____6467 =
                                      let uu____6476 =
                                        let uu____6477 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6477
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6476
                                       in
                                    [uu____6467]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6466
                                   in
                                uu____6461 FStar_Pervasives_Native.None
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
                     (lid,uu____6570,uu____6571,uu____6572,uu____6573,uu____6574)
                     -> lid
                 | uu____6583 -> failwith "Impossible!") tcs
             in
          let uu____6584 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6596,uu____6597,uu____6598,uu____6599) ->
                (lid, us)
            | uu____6608 -> failwith "Impossible!"  in
          match uu____6584 with
          | (lid,us) ->
              let uu____6617 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6617 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6644 =
                       let uu____6645 =
                         let uu____6652 = get_haseq_axiom_lid lid  in
                         (uu____6652, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6645  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6644;
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
          (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.sigelt Prims.list,
            FStar_Syntax_Syntax.sigelt Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun lids  ->
          let uu____6705 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___350_6730  ->
                    match uu___350_6730 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6731;
                        FStar_Syntax_Syntax.sigrng = uu____6732;
                        FStar_Syntax_Syntax.sigquals = uu____6733;
                        FStar_Syntax_Syntax.sigmeta = uu____6734;
                        FStar_Syntax_Syntax.sigattrs = uu____6735;_} -> true
                    | uu____6756 -> false))
             in
          match uu____6705 with
          | (tys,datas) ->
              ((let uu____6778 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___351_6787  ->
                          match uu___351_6787 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6788;
                              FStar_Syntax_Syntax.sigrng = uu____6789;
                              FStar_Syntax_Syntax.sigquals = uu____6790;
                              FStar_Syntax_Syntax.sigmeta = uu____6791;
                              FStar_Syntax_Syntax.sigattrs = uu____6792;_} ->
                              false
                          | uu____6811 -> true))
                   in
                if uu____6778
                then
                  let uu____6812 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6812
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6820 =
                       let uu____6821 = FStar_List.hd tys  in
                       uu____6821.FStar_Syntax_Syntax.sigel  in
                     match uu____6820 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6824,uvs,uu____6826,uu____6827,uu____6828,uu____6829)
                         -> uvs
                     | uu____6838 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6842 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6868 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6868 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6906,bs,t,l1,l2) ->
                                      let uu____6919 =
                                        let uu____6936 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6937 =
                                          let uu____6938 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6938
                                            t
                                           in
                                        (lid, univs2, uu____6936, uu____6937,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6919
                                  | uu____6951 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___364_6952 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___364_6952.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___364_6952.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___364_6952.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___364_6952.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6962,t,lid_t,x,l) ->
                                      let uu____6971 =
                                        let uu____6986 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6986, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6971
                                  | uu____6989 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___365_6990 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___365_6990.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___365_6990.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___365_6990.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___365_6990.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6991 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6991, tys1, datas1))
                   in
                match uu____6842 with
                | (env1,tys1,datas1) ->
                    let uu____7017 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____7056  ->
                             match uu____7056 with
                             | (env2,all_tcs,g) ->
                                 let uu____7096 = tc_tycon env2 tc  in
                                 (match uu____7096 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____7123 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____7123
                                        then
                                          let uu____7124 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7124
                                        else ());
                                       (let uu____7126 =
                                          let uu____7127 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7127
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7126))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____7017 with
                     | (env2,tcs,g) ->
                         let uu____7173 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____7195  ->
                                  match uu____7195 with
                                  | (datas2,g1) ->
                                      let uu____7214 =
                                        let uu____7219 = tc_data env2 tcs  in
                                        uu____7219 se  in
                                      (match uu____7214 with
                                       | (data,g') ->
                                           let uu____7236 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____7236)))
                             datas1 ([], g)
                            in
                         (match uu____7173 with
                          | (datas2,g1) ->
                              let uu____7257 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7275 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____7275, datas2))
                                 in
                              (match uu____7257 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____7307 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____7308 =
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
                                         uu____7307;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7308
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____7334,uu____7335)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7355 =
                                                    let uu____7360 =
                                                      let uu____7361 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____7362 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7361 uu____7362
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7360)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____7355
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____7363 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____7363 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____7379)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7410 ->
                                                             let uu____7411 =
                                                               let uu____7418
                                                                 =
                                                                 let uu____7419
                                                                   =
                                                                   let uu____7434
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____7434)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7419
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7418
                                                                in
                                                             uu____7411
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
                                                       let uu____7458 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____7458 with
                                                        | (uu____7463,inferred)
                                                            ->
                                                            let uu____7465 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____7465
                                                             with
                                                             | (uu____7470,expected)
                                                                 ->
                                                                 let uu____7472
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____7472
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7475 -> ()));
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
                          let uu____7567 =
                            let uu____7574 =
                              let uu____7575 =
                                let uu____7582 =
                                  let uu____7585 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7585  in
                                (uu____7582, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7575  in
                            FStar_Syntax_Syntax.mk uu____7574  in
                          uu____7567 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7622  ->
                                  match uu____7622 with
                                  | (x,imp) ->
                                      let uu____7641 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7641, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____7645 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7645  in
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
                               let uu____7666 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____7666
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____7667 =
                               let uu____7670 =
                                 let uu____7673 =
                                   let uu____7678 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7679 =
                                     let uu____7680 =
                                       let uu____7689 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7689
                                        in
                                     [uu____7680]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7678
                                     uu____7679
                                    in
                                 uu____7673 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____7670  in
                             FStar_Syntax_Util.refine x uu____7667  in
                           let uu____7716 =
                             let uu___366_7717 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___366_7717.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___366_7717.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7716)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7734 =
                          FStar_List.map
                            (fun uu____7758  ->
                               match uu____7758 with
                               | (x,uu____7772) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____7734 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7831  ->
                                match uu____7831 with
                                | (x,uu____7845) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____7855 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7855)
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
                               (let uu____7868 =
                                  let uu____7869 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7869.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7868)
                              in
                           let quals =
                             let uu____7873 =
                               FStar_List.filter
                                 (fun uu___352_7877  ->
                                    match uu___352_7877 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7878 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7873
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7913 =
                                 let uu____7914 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7914  in
                               FStar_Syntax_Syntax.mk_Total uu____7913  in
                             let uu____7915 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7915
                              in
                           let decl =
                             let uu____7919 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7919;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7921 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7921
                            then
                              let uu____7922 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7922
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
                                             fun uu____7973  ->
                                               match uu____7973 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7997 =
                                                       let uu____8000 =
                                                         let uu____8001 =
                                                           let uu____8008 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____8008,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____8001
                                                          in
                                                       pos uu____8000  in
                                                     (uu____7997, b)
                                                   else
                                                     (let uu____8014 =
                                                        let uu____8017 =
                                                          let uu____8018 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____8018
                                                           in
                                                        pos uu____8017  in
                                                      (uu____8014, b))))
                                      in
                                   let pat_true =
                                     let uu____8036 =
                                       let uu____8039 =
                                         let uu____8040 =
                                           let uu____8053 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____8053, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____8040
                                          in
                                       pos uu____8039  in
                                     (uu____8036,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____8087 =
                                       let uu____8090 =
                                         let uu____8091 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8091
                                          in
                                       pos uu____8090  in
                                     (uu____8087,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____8105 =
                                     let uu____8112 =
                                       let uu____8113 =
                                         let uu____8136 =
                                           let uu____8153 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____8168 =
                                             let uu____8185 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____8185]  in
                                           uu____8153 :: uu____8168  in
                                         (arg_exp, uu____8136)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8113
                                        in
                                     FStar_Syntax_Syntax.mk uu____8112  in
                                   uu____8105 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____8264 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____8264
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
                                let uu____8278 =
                                  let uu____8283 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____8283  in
                                let uu____8284 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____8278
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8284 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____8290 =
                                  let uu____8291 =
                                    let uu____8298 =
                                      let uu____8301 =
                                        let uu____8302 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____8302
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____8301]  in
                                    ((false, [lb]), uu____8298)  in
                                  FStar_Syntax_Syntax.Sig_let uu____8291  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8290;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____8314 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____8314
                               then
                                 let uu____8315 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8315
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
                                fun uu____8385  ->
                                  match uu____8385 with
                                  | (a,uu____8393) ->
                                      let uu____8398 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____8398 with
                                       | (field_name,uu____8404) ->
                                           let field_proj_tm =
                                             let uu____8406 =
                                               let uu____8407 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8407
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8406 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____8432 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8474  ->
                                    match uu____8474 with
                                    | (x,uu____8484) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____8490 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____8490 with
                                         | (field_name,uu____8498) ->
                                             let t =
                                               let uu____8502 =
                                                 let uu____8503 =
                                                   let uu____8506 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8506
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8503
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8502
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8511 =
                                                    let uu____8512 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____8512.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8511)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8528 =
                                                   FStar_List.filter
                                                     (fun uu___353_8532  ->
                                                        match uu___353_8532
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8533 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8528
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___354_8546  ->
                                                         match uu___354_8546
                                                         with
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8547 ->
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
                                               let uu____8555 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8555;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____8557 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____8557
                                               then
                                                 let uu____8558 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8558
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
                                                           fun uu____8604  ->
                                                             match uu____8604
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
                                                                   let uu____8628
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____8628,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8644
                                                                    =
                                                                    let uu____8647
                                                                    =
                                                                    let uu____8648
                                                                    =
                                                                    let uu____8655
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8655,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8648
                                                                     in
                                                                    pos
                                                                    uu____8647
                                                                     in
                                                                    (uu____8644,
                                                                    b))
                                                                   else
                                                                    (let uu____8661
                                                                    =
                                                                    let uu____8664
                                                                    =
                                                                    let uu____8665
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8665
                                                                     in
                                                                    pos
                                                                    uu____8664
                                                                     in
                                                                    (uu____8661,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____8683 =
                                                     let uu____8686 =
                                                       let uu____8687 =
                                                         let uu____8700 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____8700,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8687
                                                        in
                                                     pos uu____8686  in
                                                   let uu____8709 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____8683,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8709)
                                                    in
                                                 let body =
                                                   let uu____8725 =
                                                     let uu____8732 =
                                                       let uu____8733 =
                                                         let uu____8756 =
                                                           let uu____8773 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____8773]  in
                                                         (arg_exp,
                                                           uu____8756)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8733
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8732
                                                      in
                                                   uu____8725
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____8841 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____8841
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
                                                   let uu____8852 =
                                                     let uu____8857 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____8857
                                                      in
                                                   let uu____8858 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8852;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8858;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____8864 =
                                                     let uu____8865 =
                                                       let uu____8872 =
                                                         let uu____8875 =
                                                           let uu____8876 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____8876
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____8875]  in
                                                       ((false, [lb]),
                                                         uu____8872)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8865
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8864;
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
                                                 (let uu____8888 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____8888
                                                  then
                                                    let uu____8889 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8889
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____8432 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8937) when
              let uu____8942 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8942 ->
              let uu____8943 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8943 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8965 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8965 with
                    | (formals,uu____8983) ->
                        let uu____9004 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____9036 =
                                   let uu____9037 =
                                     let uu____9038 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____9038  in
                                   FStar_Ident.lid_equals typ_lid uu____9037
                                    in
                                 if uu____9036
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9057,uvs',tps,typ0,uu____9061,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____9078 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9119 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9119
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____9004 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9146 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9146 with
                              | (indices,uu____9164) ->
                                  let refine_domain =
                                    let uu____9186 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___355_9191  ->
                                              match uu___355_9191 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9192 -> true
                                              | uu____9201 -> false))
                                       in
                                    if uu____9186
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___356_9211 =
                                      match uu___356_9211 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9214,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9226 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9227 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9227 with
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
                                    let uu____9238 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9238 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9321  ->
                                               fun uu____9322  ->
                                                 match (uu____9321,
                                                         uu____9322)
                                                 with
                                                 | ((x,uu____9348),(x',uu____9350))
                                                     ->
                                                     let uu____9371 =
                                                       let uu____9378 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9378)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9371) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9383 -> []
  