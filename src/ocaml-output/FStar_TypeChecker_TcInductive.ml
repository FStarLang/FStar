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
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4077,uu____4078,t,uu____4080,uu____4081,uu____4082) -> t
    | uu____4087 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4107 =
         let uu____4108 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4108 haseq_suffix  in
       uu____4107 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4128 =
      let uu____4131 =
        let uu____4134 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4134]  in
      FStar_List.append lid.FStar_Ident.ns uu____4131  in
    FStar_Ident.lid_of_ids uu____4128
  
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
          let uu____4179 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4193,bs,t,uu____4196,uu____4197) -> (lid, bs, t)
            | uu____4206 -> failwith "Impossible!"  in
          match uu____4179 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4228 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4228 t  in
              let uu____4237 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4237 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4255 =
                       let uu____4256 = FStar_Syntax_Subst.compress t2  in
                       uu____4256.FStar_Syntax_Syntax.n  in
                     match uu____4255 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4260) -> ibs
                     | uu____4281 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4290 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4291 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4290 uu____4291
                      in
                   let ind1 =
                     let uu____4297 =
                       let uu____4302 =
                         FStar_List.map
                           (fun uu____4319  ->
                              match uu____4319 with
                              | (bv,aq) ->
                                  let uu____4338 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4338, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4302  in
                     uu____4297 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4346 =
                       let uu____4351 =
                         FStar_List.map
                           (fun uu____4368  ->
                              match uu____4368 with
                              | (bv,aq) ->
                                  let uu____4387 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4387, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4351  in
                     uu____4346 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4395 =
                       let uu____4400 =
                         let uu____4401 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4401]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4400
                        in
                     uu____4395 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4452 =
                            let uu____4453 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4453  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4452) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4466 =
                              let uu____4469 =
                                let uu____4474 =
                                  let uu____4475 =
                                    let uu____4484 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4484  in
                                  [uu____4475]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4474
                                 in
                              uu____4469 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4466)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___362_4509 = fml  in
                     let uu____4510 =
                       let uu____4511 =
                         let uu____4518 =
                           let uu____4519 =
                             let uu____4532 =
                               let uu____4543 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4543]  in
                             [uu____4532]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4519  in
                         (fml, uu____4518)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4511  in
                     {
                       FStar_Syntax_Syntax.n = uu____4510;
                       FStar_Syntax_Syntax.pos =
                         (uu___362_4509.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___362_4509.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4598 =
                              let uu____4603 =
                                let uu____4604 =
                                  let uu____4613 =
                                    let uu____4614 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4614 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4613  in
                                [uu____4604]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4603
                               in
                            uu____4598 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4671 =
                              let uu____4676 =
                                let uu____4677 =
                                  let uu____4686 =
                                    let uu____4687 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4687 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4686  in
                                [uu____4677]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4676
                               in
                            uu____4671 FStar_Pervasives_Native.None
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
          let uu____4763 =
            let uu____4764 = FStar_Syntax_Subst.compress dt1  in
            uu____4764.FStar_Syntax_Syntax.n  in
          match uu____4763 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4768) ->
              let dbs1 =
                let uu____4798 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4798  in
              let dbs2 =
                let uu____4848 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4848 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4863 =
                           let uu____4868 =
                             let uu____4869 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4869]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4868
                            in
                         uu____4863 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4902 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4902 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4910 =
                       let uu____4915 =
                         let uu____4916 =
                           let uu____4925 =
                             let uu____4926 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4926
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4925  in
                         [uu____4916]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4915
                        in
                     uu____4910 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4975 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5065,uu____5066,uu____5067,uu____5068,uu____5069)
                  -> lid
              | uu____5078 -> failwith "Impossible!"  in
            let uu____5079 = acc  in
            match uu____5079 with
            | (uu____5116,en,uu____5118,uu____5119) ->
                let uu____5140 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5140 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5177 = acc  in
                     (match uu____5177 with
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
                                     (uu____5251,uu____5252,uu____5253,t_lid,uu____5255,uu____5256)
                                     -> t_lid = lid
                                 | uu____5261 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5274 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5274)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5277 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5280 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5277, uu____5280)))
  
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
          let uu____5337 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5347,us,uu____5349,t,uu____5351,uu____5352) -> 
                (us, t)
            | uu____5361 -> failwith "Impossible!"  in
          match uu____5337 with
          | (us,t) ->
              let uu____5370 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5370 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5395 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5395 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5473 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5473 with
                           | (uu____5488,t1) ->
                               let uu____5510 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5510
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5512 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5512 with
                          | (phi1,uu____5520) ->
                              ((let uu____5522 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5522
                                then
                                  let uu____5523 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5523
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5540  ->
                                         match uu____5540 with
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
                let uu____5608 =
                  let uu____5609 = FStar_Syntax_Subst.compress t  in
                  uu____5609.FStar_Syntax_Syntax.n  in
                match uu____5608 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5616) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5653 = is_mutual t'  in
                    if uu____5653
                    then true
                    else
                      (let uu____5655 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5655)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5675) -> is_mutual t'
                | uu____5680 -> false
              
              and exists_mutual uu___349_5681 =
                match uu___349_5681 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5700 =
                let uu____5701 = FStar_Syntax_Subst.compress dt1  in
                uu____5701.FStar_Syntax_Syntax.n  in
              match uu____5700 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5707) ->
                  let dbs1 =
                    let uu____5737 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5737  in
                  let dbs2 =
                    let uu____5787 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5787 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5807 =
                               let uu____5812 =
                                 let uu____5813 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5813]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5812
                                in
                             uu____5807 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5845 = is_mutual sort  in
                             if uu____5845
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
                           let uu____5857 =
                             let uu____5862 =
                               let uu____5863 =
                                 let uu____5872 =
                                   let uu____5873 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5873 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5872  in
                               [uu____5863]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5862
                              in
                           uu____5857 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5922 -> acc
  
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
              let uu____5971 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5993,bs,t,uu____5996,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6008 -> failwith "Impossible!"  in
              match uu____5971 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6031 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6031 t  in
                  let uu____6040 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6040 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6050 =
                           let uu____6051 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6051.FStar_Syntax_Syntax.n  in
                         match uu____6050 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6055) ->
                             ibs
                         | uu____6076 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6085 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6086 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6085
                           uu____6086
                          in
                       let ind1 =
                         let uu____6092 =
                           let uu____6097 =
                             FStar_List.map
                               (fun uu____6114  ->
                                  match uu____6114 with
                                  | (bv,aq) ->
                                      let uu____6133 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6133, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6097  in
                         uu____6092 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6141 =
                           let uu____6146 =
                             FStar_List.map
                               (fun uu____6163  ->
                                  match uu____6163 with
                                  | (bv,aq) ->
                                      let uu____6182 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6182, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6146  in
                         uu____6141 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6190 =
                           let uu____6195 =
                             let uu____6196 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6196]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6195
                            in
                         uu____6190 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6234,uu____6235,uu____6236,t_lid,uu____6238,uu____6239)
                                  -> t_lid = lid
                              | uu____6244 -> failwith "Impossible")
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
                         let uu___363_6254 = fml  in
                         let uu____6255 =
                           let uu____6256 =
                             let uu____6263 =
                               let uu____6264 =
                                 let uu____6277 =
                                   let uu____6288 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____6288]  in
                                 [uu____6277]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6264
                                in
                             (fml, uu____6263)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6256  in
                         {
                           FStar_Syntax_Syntax.n = uu____6255;
                           FStar_Syntax_Syntax.pos =
                             (uu___363_6254.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___363_6254.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6343 =
                                  let uu____6348 =
                                    let uu____6349 =
                                      let uu____6358 =
                                        let uu____6359 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6359
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6358
                                       in
                                    [uu____6349]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6348
                                   in
                                uu____6343 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6416 =
                                  let uu____6421 =
                                    let uu____6422 =
                                      let uu____6431 =
                                        let uu____6432 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6432
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6431
                                       in
                                    [uu____6422]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6421
                                   in
                                uu____6416 FStar_Pervasives_Native.None
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
                     (lid,uu____6525,uu____6526,uu____6527,uu____6528,uu____6529)
                     -> lid
                 | uu____6538 -> failwith "Impossible!") tcs
             in
          let uu____6539 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6551,uu____6552,uu____6553,uu____6554) ->
                (lid, us)
            | uu____6563 -> failwith "Impossible!"  in
          match uu____6539 with
          | (lid,us) ->
              let uu____6572 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6572 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6599 =
                       let uu____6600 =
                         let uu____6607 = get_haseq_axiom_lid lid  in
                         (uu____6607, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6600  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6599;
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
          let uu____6660 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___350_6685  ->
                    match uu___350_6685 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6686;
                        FStar_Syntax_Syntax.sigrng = uu____6687;
                        FStar_Syntax_Syntax.sigquals = uu____6688;
                        FStar_Syntax_Syntax.sigmeta = uu____6689;
                        FStar_Syntax_Syntax.sigattrs = uu____6690;_} -> true
                    | uu____6711 -> false))
             in
          match uu____6660 with
          | (tys,datas) ->
              ((let uu____6733 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___351_6742  ->
                          match uu___351_6742 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6743;
                              FStar_Syntax_Syntax.sigrng = uu____6744;
                              FStar_Syntax_Syntax.sigquals = uu____6745;
                              FStar_Syntax_Syntax.sigmeta = uu____6746;
                              FStar_Syntax_Syntax.sigattrs = uu____6747;_} ->
                              false
                          | uu____6766 -> true))
                   in
                if uu____6733
                then
                  let uu____6767 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6767
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6775 =
                       let uu____6776 = FStar_List.hd tys  in
                       uu____6776.FStar_Syntax_Syntax.sigel  in
                     match uu____6775 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6779,uvs,uu____6781,uu____6782,uu____6783,uu____6784)
                         -> uvs
                     | uu____6793 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6797 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6823 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6823 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6861,bs,t,l1,l2) ->
                                      let uu____6874 =
                                        let uu____6891 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6892 =
                                          let uu____6893 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6893
                                            t
                                           in
                                        (lid, univs2, uu____6891, uu____6892,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6874
                                  | uu____6906 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___364_6907 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___364_6907.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___364_6907.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___364_6907.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___364_6907.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6917,t,lid_t,x,l) ->
                                      let uu____6926 =
                                        let uu____6941 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6941, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6926
                                  | uu____6944 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___365_6945 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___365_6945.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___365_6945.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___365_6945.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___365_6945.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6946 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6946, tys1, datas1))
                   in
                match uu____6797 with
                | (env1,tys1,datas1) ->
                    let uu____6972 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____7011  ->
                             match uu____7011 with
                             | (env2,all_tcs,g) ->
                                 let uu____7051 = tc_tycon env2 tc  in
                                 (match uu____7051 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____7078 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____7078
                                        then
                                          let uu____7079 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7079
                                        else ());
                                       (let uu____7081 =
                                          let uu____7082 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7082
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7081))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____6972 with
                     | (env2,tcs,g) ->
                         let uu____7128 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____7150  ->
                                  match uu____7150 with
                                  | (datas2,g1) ->
                                      let uu____7169 =
                                        let uu____7174 = tc_data env2 tcs  in
                                        uu____7174 se  in
                                      (match uu____7169 with
                                       | (data,g') ->
                                           let uu____7191 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____7191)))
                             datas1 ([], g)
                            in
                         (match uu____7128 with
                          | (datas2,g1) ->
                              let uu____7212 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7230 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____7230, datas2))
                                 in
                              (match uu____7212 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____7262 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____7263 =
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
                                         uu____7262;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7263
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____7289,uu____7290)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7310 =
                                                    let uu____7315 =
                                                      let uu____7316 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____7317 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7316 uu____7317
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7315)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____7310
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____7318 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____7318 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____7334)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7365 ->
                                                             let uu____7366 =
                                                               let uu____7373
                                                                 =
                                                                 let uu____7374
                                                                   =
                                                                   let uu____7389
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____7389)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7374
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7373
                                                                in
                                                             uu____7366
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
                                                       let uu____7413 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____7413 with
                                                        | (uu____7418,inferred)
                                                            ->
                                                            let uu____7420 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____7420
                                                             with
                                                             | (uu____7425,expected)
                                                                 ->
                                                                 let uu____7427
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____7427
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7430 -> ()));
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
                          let uu____7522 =
                            let uu____7529 =
                              let uu____7530 =
                                let uu____7537 =
                                  let uu____7540 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7540  in
                                (uu____7537, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7530  in
                            FStar_Syntax_Syntax.mk uu____7529  in
                          uu____7522 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7577  ->
                                  match uu____7577 with
                                  | (x,imp) ->
                                      let uu____7596 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7596, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____7600 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7600  in
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
                               let uu____7621 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____7621
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____7622 =
                               let uu____7625 =
                                 let uu____7628 =
                                   let uu____7633 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7634 =
                                     let uu____7635 =
                                       let uu____7644 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7644
                                        in
                                     [uu____7635]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7633
                                     uu____7634
                                    in
                                 uu____7628 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____7625  in
                             FStar_Syntax_Util.refine x uu____7622  in
                           let uu____7671 =
                             let uu___366_7672 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___366_7672.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___366_7672.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7671)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7689 =
                          FStar_List.map
                            (fun uu____7713  ->
                               match uu____7713 with
                               | (x,uu____7727) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____7689 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7786  ->
                                match uu____7786 with
                                | (x,uu____7800) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____7810 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7810)
                          &&
                          (((tc.FStar_Ident.ident).FStar_Ident.idText =
                              "dtuple2")
                             ||
                             (FStar_List.existsb
                                (fun s  ->
                                   s =
                                     (tc.FStar_Ident.ident).FStar_Ident.idText)
                                early_prims_inductives))
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
                               (let uu____7823 =
                                  let uu____7824 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7824.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7823)
                              in
                           let quals =
                             let uu____7828 =
                               FStar_List.filter
                                 (fun uu___352_7832  ->
                                    match uu___352_7832 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7833 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7828
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7868 =
                                 let uu____7869 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7869  in
                               FStar_Syntax_Syntax.mk_Total uu____7868  in
                             let uu____7870 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7870
                              in
                           let decl =
                             let uu____7874 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7874;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7876 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7876
                            then
                              let uu____7877 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7877
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
                                             fun uu____7928  ->
                                               match uu____7928 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7952 =
                                                       let uu____7955 =
                                                         let uu____7956 =
                                                           let uu____7963 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7963,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7956
                                                          in
                                                       pos uu____7955  in
                                                     (uu____7952, b)
                                                   else
                                                     (let uu____7969 =
                                                        let uu____7972 =
                                                          let uu____7973 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7973
                                                           in
                                                        pos uu____7972  in
                                                      (uu____7969, b))))
                                      in
                                   let pat_true =
                                     let uu____7991 =
                                       let uu____7994 =
                                         let uu____7995 =
                                           let uu____8008 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____8008, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7995
                                          in
                                       pos uu____7994  in
                                     (uu____7991,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____8042 =
                                       let uu____8045 =
                                         let uu____8046 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8046
                                          in
                                       pos uu____8045  in
                                     (uu____8042,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____8060 =
                                     let uu____8067 =
                                       let uu____8068 =
                                         let uu____8091 =
                                           let uu____8108 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____8123 =
                                             let uu____8140 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____8140]  in
                                           uu____8108 :: uu____8123  in
                                         (arg_exp, uu____8091)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8068
                                        in
                                     FStar_Syntax_Syntax.mk uu____8067  in
                                   uu____8060 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____8219 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____8219
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
                                let uu____8233 =
                                  let uu____8238 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____8238  in
                                let uu____8239 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____8233
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8239 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____8245 =
                                  let uu____8246 =
                                    let uu____8253 =
                                      let uu____8256 =
                                        let uu____8257 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____8257
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____8256]  in
                                    ((false, [lb]), uu____8253)  in
                                  FStar_Syntax_Syntax.Sig_let uu____8246  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8245;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____8269 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____8269
                               then
                                 let uu____8270 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8270
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
                                fun uu____8340  ->
                                  match uu____8340 with
                                  | (a,uu____8348) ->
                                      let uu____8353 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____8353 with
                                       | (field_name,uu____8359) ->
                                           let field_proj_tm =
                                             let uu____8361 =
                                               let uu____8362 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8362
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8361 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____8387 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8429  ->
                                    match uu____8429 with
                                    | (x,uu____8439) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____8445 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____8445 with
                                         | (field_name,uu____8453) ->
                                             let t =
                                               let uu____8457 =
                                                 let uu____8458 =
                                                   let uu____8461 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8461
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8458
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8457
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8466 =
                                                    let uu____8467 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____8467.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8466)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8483 =
                                                   FStar_List.filter
                                                     (fun uu___353_8487  ->
                                                        match uu___353_8487
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8488 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8483
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___354_8501  ->
                                                         match uu___354_8501
                                                         with
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8502 ->
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
                                               let uu____8510 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8510;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____8512 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____8512
                                               then
                                                 let uu____8513 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8513
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
                                                           fun uu____8559  ->
                                                             match uu____8559
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
                                                                   let uu____8583
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____8583,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8599
                                                                    =
                                                                    let uu____8602
                                                                    =
                                                                    let uu____8603
                                                                    =
                                                                    let uu____8610
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8610,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8603
                                                                     in
                                                                    pos
                                                                    uu____8602
                                                                     in
                                                                    (uu____8599,
                                                                    b))
                                                                   else
                                                                    (let uu____8616
                                                                    =
                                                                    let uu____8619
                                                                    =
                                                                    let uu____8620
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8620
                                                                     in
                                                                    pos
                                                                    uu____8619
                                                                     in
                                                                    (uu____8616,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____8638 =
                                                     let uu____8641 =
                                                       let uu____8642 =
                                                         let uu____8655 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____8655,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8642
                                                        in
                                                     pos uu____8641  in
                                                   let uu____8664 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____8638,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8664)
                                                    in
                                                 let body =
                                                   let uu____8680 =
                                                     let uu____8687 =
                                                       let uu____8688 =
                                                         let uu____8711 =
                                                           let uu____8728 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____8728]  in
                                                         (arg_exp,
                                                           uu____8711)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8688
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8687
                                                      in
                                                   uu____8680
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____8796 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____8796
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
                                                   let uu____8807 =
                                                     let uu____8812 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____8812
                                                      in
                                                   let uu____8813 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8807;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8813;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____8819 =
                                                     let uu____8820 =
                                                       let uu____8827 =
                                                         let uu____8830 =
                                                           let uu____8831 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____8831
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____8830]  in
                                                       ((false, [lb]),
                                                         uu____8827)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8820
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8819;
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
                                                 (let uu____8843 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____8843
                                                  then
                                                    let uu____8844 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8844
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____8387 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8892) when
              let uu____8897 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8897 ->
              let uu____8898 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8898 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8920 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8920 with
                    | (formals,uu____8938) ->
                        let uu____8959 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8991 =
                                   let uu____8992 =
                                     let uu____8993 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8993  in
                                   FStar_Ident.lid_equals typ_lid uu____8992
                                    in
                                 if uu____8991
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9012,uvs',tps,typ0,uu____9016,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____9033 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9074 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9074
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____8959 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9101 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9101 with
                              | (indices,uu____9119) ->
                                  let refine_domain =
                                    let uu____9141 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___355_9146  ->
                                              match uu___355_9146 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9147 -> true
                                              | uu____9156 -> false))
                                       in
                                    if uu____9141
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___356_9166 =
                                      match uu___356_9166 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9169,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9181 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9182 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9182 with
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
                                    let uu____9193 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9193 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9276  ->
                                               fun uu____9277  ->
                                                 match (uu____9276,
                                                         uu____9277)
                                                 with
                                                 | ((x,uu____9303),(x',uu____9305))
                                                     ->
                                                     let uu____9326 =
                                                       let uu____9333 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9333)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9326) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9338 -> []
  