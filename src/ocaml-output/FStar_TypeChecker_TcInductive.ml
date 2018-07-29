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
                                FStar_Syntax_Util.arrow_formals k2  in
                              (match uu____143 with
                               | (indices,t) ->
                                   let uu____188 =
                                     FStar_TypeChecker_TcTerm.tc_binders
                                       env_tps indices
                                      in
                                   (match uu____188 with
                                    | (indices1,env',guard_indices,us') ->
                                        let uu____209 =
                                          let uu____216 =
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              env' t
                                             in
                                          match uu____216 with
                                          | (t1,uu____230,g) ->
                                              let uu____232 =
                                                let uu____233 =
                                                  let uu____234 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_indices g
                                                     in
                                                  FStar_TypeChecker_Env.conj_guard
                                                    guard_params uu____234
                                                   in
                                                FStar_TypeChecker_Rel.discharge_guard
                                                  env' uu____233
                                                 in
                                              (t1, uu____232)
                                           in
                                        (match uu____209 with
                                         | (t1,guard) ->
                                             let k3 =
                                               let uu____254 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   t1
                                                  in
                                               FStar_Syntax_Util.arrow
                                                 indices1 uu____254
                                                in
                                             let uu____257 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____257 with
                                              | (t_type,u) ->
                                                  ((let uu____273 =
                                                      let uu____274 =
                                                        FStar_TypeChecker_Rel.subtype_nosmt_force
                                                          env1 t1 t_type
                                                         in
                                                      Prims.op_Negation
                                                        uu____274
                                                       in
                                                    if uu____273
                                                    then
                                                      let uu____275 =
                                                        let uu____280 =
                                                          let uu____281 =
                                                            FStar_Syntax_Print.term_to_string
                                                              t1
                                                             in
                                                          let uu____282 =
                                                            FStar_Ident.string_of_lid
                                                              tc
                                                             in
                                                          FStar_Util.format2
                                                            "Type annotation %s for inductive %s is not a subtype of Type"
                                                            uu____281
                                                            uu____282
                                                           in
                                                        (FStar_Errors.Error_InductiveAnnotNotAType,
                                                          uu____280)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____275
                                                        s.FStar_Syntax_Syntax.sigrng
                                                    else ());
                                                   (let usubst1 =
                                                      FStar_Syntax_Subst.univ_var_closing
                                                        uvs1
                                                       in
                                                    let guard1 =
                                                      FStar_TypeChecker_Util.close_guard_implicits
                                                        env1
                                                        (FStar_List.append
                                                           tps3 indices1)
                                                        guard
                                                       in
                                                    let t_tc =
                                                      let uu____297 =
                                                        let uu____306 =
                                                          FStar_All.pipe_right
                                                            tps3
                                                            (FStar_Syntax_Subst.subst_binders
                                                               usubst1)
                                                           in
                                                        let uu____323 =
                                                          let uu____332 =
                                                            let uu____345 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                (FStar_List.length
                                                                   tps3)
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst_binders
                                                              uu____345
                                                             in
                                                          FStar_All.pipe_right
                                                            indices1
                                                            uu____332
                                                           in
                                                        FStar_List.append
                                                          uu____306 uu____323
                                                         in
                                                      let uu____368 =
                                                        let uu____371 =
                                                          let uu____372 =
                                                            let uu____377 =
                                                              FStar_Syntax_Subst.shift_subst
                                                                ((FStar_List.length
                                                                    tps3)
                                                                   +
                                                                   (FStar_List.length
                                                                    indices1))
                                                                usubst1
                                                               in
                                                            FStar_Syntax_Subst.subst
                                                              uu____377
                                                             in
                                                          FStar_All.pipe_right
                                                            t1 uu____372
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____371
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____297 uu____368
                                                       in
                                                    let tps4 =
                                                      FStar_Syntax_Subst.close_binders
                                                        tps3
                                                       in
                                                    let k4 =
                                                      FStar_Syntax_Subst.close
                                                        tps4 k3
                                                       in
                                                    let uu____394 =
                                                      let uu____399 =
                                                        FStar_Syntax_Subst.subst_binders
                                                          usubst1 tps4
                                                         in
                                                      let uu____400 =
                                                        let uu____401 =
                                                          FStar_Syntax_Subst.shift_subst
                                                            (FStar_List.length
                                                               tps4) usubst1
                                                           in
                                                        FStar_Syntax_Subst.subst
                                                          uu____401 k4
                                                         in
                                                      (uu____399, uu____400)
                                                       in
                                                    match uu____394 with
                                                    | (tps5,k5) ->
                                                        let fv_tc =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            tc
                                                            FStar_Syntax_Syntax.delta_constant
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let uu____421 =
                                                          FStar_TypeChecker_Env.push_let_binding
                                                            env0
                                                            (FStar_Util.Inr
                                                               fv_tc)
                                                            (uvs1, t_tc)
                                                           in
                                                        (uu____421,
                                                          (let uu___348_427 =
                                                             s  in
                                                           {
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               (FStar_Syntax_Syntax.Sig_inductive_typ
                                                                  (tc, uvs1,
                                                                    tps5, k5,
                                                                    mutuals,
                                                                    data));
                                                             FStar_Syntax_Syntax.sigrng
                                                               =
                                                               (uu___348_427.FStar_Syntax_Syntax.sigrng);
                                                             FStar_Syntax_Syntax.sigquals
                                                               =
                                                               (uu___348_427.FStar_Syntax_Syntax.sigquals);
                                                             FStar_Syntax_Syntax.sigmeta
                                                               =
                                                               (uu___348_427.FStar_Syntax_Syntax.sigmeta);
                                                             FStar_Syntax_Syntax.sigattrs
                                                               =
                                                               (uu___348_427.FStar_Syntax_Syntax.sigattrs)
                                                           }), u, guard1)))))))))))
      | uu____432 -> failwith "impossible"
  
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
            let uu____492 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____492 with
             | (usubst,_uvs1) ->
                 let uu____515 =
                   let uu____520 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____521 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____520, uu____521)  in
                 (match uu____515 with
                  | (env1,t1) ->
                      let uu____528 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____567  ->
                               match uu____567 with
                               | (se1,u_tc) ->
                                   let uu____582 =
                                     let uu____583 =
                                       let uu____584 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____584  in
                                     FStar_Ident.lid_equals tc_lid uu____583
                                      in
                                   if uu____582
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____603,uu____604,tps,uu____606,uu____607,uu____608)
                                          ->
                                          let tps1 =
                                            let uu____618 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____618
                                              (FStar_List.map
                                                 (fun uu____658  ->
                                                    match uu____658 with
                                                    | (x,uu____672) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____680 =
                                            let uu____687 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____687, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____680
                                      | uu____694 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____735 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____735
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____528 with
                       | (env2,tps,u_tc) ->
                           let uu____762 =
                             let t2 =
                               FStar_TypeChecker_Normalize.unfold_whnf env2
                                 t1
                                in
                             let uu____778 =
                               let uu____779 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____779.FStar_Syntax_Syntax.n  in
                             match uu____778 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____818 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____818 with
                                  | (uu____859,bs') ->
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
                                                fun uu____930  ->
                                                  match uu____930 with
                                                  | (x,uu____938) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____943 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____943)
                             | uu____944 -> ([], t2)  in
                           (match uu____762 with
                            | (arguments,result) ->
                                ((let uu____988 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____988
                                  then
                                    let uu____989 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____990 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____991 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____989 uu____990 uu____991
                                  else ());
                                 (let uu____993 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____993 with
                                  | (arguments1,env',us) ->
                                      let uu____1007 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env' result
                                         in
                                      (match uu____1007 with
                                       | (result1,res_lcomp) ->
                                           let ty =
                                             let uu____1019 =
                                               unfold_whnf env2
                                                 res_lcomp.FStar_Syntax_Syntax.res_typ
                                                in
                                             FStar_All.pipe_right uu____1019
                                               FStar_Syntax_Util.unrefine
                                              in
                                           ((let uu____1021 =
                                               let uu____1022 =
                                                 FStar_Syntax_Subst.compress
                                                   ty
                                                  in
                                               uu____1022.FStar_Syntax_Syntax.n
                                                in
                                             match uu____1021 with
                                             | FStar_Syntax_Syntax.Tm_type
                                                 uu____1025 -> ()
                                             | uu____1026 ->
                                                 let uu____1027 =
                                                   let uu____1032 =
                                                     let uu____1033 =
                                                       FStar_Syntax_Print.term_to_string
                                                         result1
                                                        in
                                                     let uu____1034 =
                                                       FStar_Syntax_Print.term_to_string
                                                         ty
                                                        in
                                                     FStar_Util.format2
                                                       "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                       uu____1033 uu____1034
                                                      in
                                                   (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                     uu____1032)
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____1027
                                                   se.FStar_Syntax_Syntax.sigrng);
                                            (let uu____1035 =
                                               FStar_Syntax_Util.head_and_args
                                                 result1
                                                in
                                             match uu____1035 with
                                             | (head1,uu____1057) ->
                                                 let g_uvs =
                                                   let uu____1083 =
                                                     let uu____1084 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____1084.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1083 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       ({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_fvar
                                                            fv;
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____1088;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____1089;_},tuvs)
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
                                                                  let uu____1102
                                                                    =
                                                                    let uu____1103
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1104
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
                                                                    uu____1103
                                                                    uu____1104
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1102)
                                                           FStar_TypeChecker_Env.trivial_guard
                                                           tuvs _uvs1
                                                       else
                                                         failwith
                                                           "Impossible: tc_datacon: length of annotated universes not same as instantiated ones"
                                                   | FStar_Syntax_Syntax.Tm_fvar
                                                       fv when
                                                       FStar_Syntax_Syntax.fv_eq_lid
                                                         fv tc_lid
                                                       ->
                                                       FStar_TypeChecker_Env.trivial_guard
                                                   | uu____1107 ->
                                                       let uu____1108 =
                                                         let uu____1113 =
                                                           let uu____1114 =
                                                             FStar_Syntax_Print.lid_to_string
                                                               tc_lid
                                                              in
                                                           let uu____1115 =
                                                             FStar_Syntax_Print.term_to_string
                                                               head1
                                                              in
                                                           FStar_Util.format2
                                                             "Expected a constructor of type %s; got %s"
                                                             uu____1114
                                                             uu____1115
                                                            in
                                                         (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                           uu____1113)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1108
                                                         se.FStar_Syntax_Syntax.sigrng
                                                    in
                                                 let g =
                                                   FStar_List.fold_left2
                                                     (fun g  ->
                                                        fun uu____1130  ->
                                                          fun u_x  ->
                                                            match uu____1130
                                                            with
                                                            | (x,uu____1139)
                                                                ->
                                                                let uu____1144
                                                                  =
                                                                  FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                   in
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  g
                                                                  uu____1144)
                                                     g_uvs arguments1 us
                                                    in
                                                 let t2 =
                                                   let uu____1148 =
                                                     let uu____1157 =
                                                       FStar_All.pipe_right
                                                         tps
                                                         (FStar_List.map
                                                            (fun uu____1197 
                                                               ->
                                                               match uu____1197
                                                               with
                                                               | (x,uu____1211)
                                                                   ->
                                                                   (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                        in
                                                     FStar_List.append
                                                       uu____1157 arguments1
                                                      in
                                                   let uu____1224 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       result1
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____1148 uu____1224
                                                    in
                                                 let t3 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     _uvs1 t2
                                                    in
                                                 ((let uu___349_1229 = se  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (c, _uvs1, t3,
                                                            tc_lid, ntps, []));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___349_1229.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___349_1229.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___349_1229.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___349_1229.FStar_Syntax_Syntax.sigattrs)
                                                   }), g))))))))))
        | uu____1232 -> failwith "impossible"
  
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
            let uu___350_1297 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___350_1297.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___350_1297.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___350_1297.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1307 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1307
           then
             let uu____1308 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1308
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1348  ->
                     match uu____1348 with
                     | (se,uu____1354) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1355,uu____1356,tps,k,uu____1359,uu____1360)
                              ->
                              let uu____1369 =
                                let uu____1370 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1370
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1369
                          | uu____1375 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1403,uu____1404,t,uu____1406,uu____1407,uu____1408)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1413 -> failwith "Impossible"))
              in
           let t =
             let uu____1417 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1417
              in
           (let uu____1427 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1427
            then
              let uu____1428 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1428
            else ());
           (let uu____1430 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1430 with
            | (uvs,t1) ->
                ((let uu____1450 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1450
                  then
                    let uu____1451 =
                      let uu____1452 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1452
                        (FStar_String.concat ", ")
                       in
                    let uu____1463 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1451 uu____1463
                  else ());
                 (let uu____1465 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1465 with
                  | (uvs1,t2) ->
                      let uu____1480 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1480 with
                       | (args,uu____1504) ->
                           let uu____1525 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1525 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1630  ->
                                       fun uu____1631  ->
                                         match (uu____1630, uu____1631) with
                                         | ((x,uu____1653),(se,uu____1655))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1671,tps,uu____1673,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1685 =
                                                    let uu____1690 =
                                                      let uu____1691 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1691.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1690 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1720 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1720
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____1798
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____1817 -> ([], ty)
                                                     in
                                                  (match uu____1685 with
                                                   | (tps1,t3) ->
                                                       let uu___351_1826 = se
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
                                                           (uu___351_1826.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___351_1826.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___351_1826.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___351_1826.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____1831 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____1837 ->
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
                                             (fun uu___339_1859  ->
                                                match uu___339_1859 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____1865,uu____1866,uu____1867,uu____1868,uu____1869);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____1870;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____1871;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____1872;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____1873;_}
                                                    -> (tc, uvs_universes)
                                                | uu____1886 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____1909  ->
                                           fun d  ->
                                             match uu____1909 with
                                             | (t3,uu____1918) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____1924,uu____1925,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____1934 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____1934
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___352_1935 = d
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
                                                          (uu___352_1935.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___352_1935.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___352_1935.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___352_1935.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____1938 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____1953 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____1953
      then
        FStar_Util.print_string
          (Prims.strcat "Positivity::" (Prims.strcat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____1965 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____1965
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____1981 =
      let uu____1982 = FStar_Syntax_Subst.compress t  in
      uu____1982.FStar_Syntax_Syntax.n  in
    match uu____1981 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2001 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2006 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____2059 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2128  ->
               match uu____2128 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2171 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2171  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2059
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2415 =
             let uu____2416 = FStar_Syntax_Print.term_to_string btype  in
             Prims.strcat "Checking strict positivity in type: " uu____2416
              in
           debug_log env uu____2415);
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
           (let uu____2419 =
              let uu____2420 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.strcat
                "Checking strict positivity in type, after normalization: "
                uu____2420
               in
            debug_log env uu____2419);
           (let uu____2423 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2423) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2434 =
                  let uu____2435 = FStar_Syntax_Subst.compress btype1  in
                  uu____2435.FStar_Syntax_Syntax.n  in
                match uu____2434 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2464 = try_get_fv t  in
                    (match uu____2464 with
                     | (fv,us) ->
                         let uu____2471 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2471
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2483  ->
                                 match uu____2483 with
                                 | (t1,uu____2491) ->
                                     let uu____2496 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2496) args)
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
                          let uu____2546 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2546
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2550 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2550
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
                            (fun uu____2570  ->
                               match uu____2570 with
                               | (b,uu____2578) ->
                                   let uu____2583 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2583) sbs)
                           &&
                           ((let uu____2588 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2588 with
                             | (uu____2593,return_type) ->
                                 let uu____2595 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2595)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2616 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2618 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2621) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2648) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2674,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2732  ->
                          match uu____2732 with
                          | (p,uu____2744,t) ->
                              let bs =
                                let uu____2763 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2763
                                 in
                              let uu____2772 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2772 with
                               | (bs1,t1) ->
                                   let uu____2779 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2779)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2801,uu____2802)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2864 ->
                    ((let uu____2866 =
                        let uu____2867 =
                          let uu____2868 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2869 =
                            let uu____2870 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.strcat " and term: " uu____2870  in
                          Prims.strcat uu____2868 uu____2869  in
                        Prims.strcat
                          "Checking strict positivity, unexpected tag: "
                          uu____2867
                         in
                      debug_log env uu____2866);
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
              (let uu____2888 =
                 let uu____2889 =
                   let uu____2890 =
                     let uu____2891 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.strcat " applied to arguments: " uu____2891  in
                   Prims.strcat ilid.FStar_Ident.str uu____2890  in
                 Prims.strcat "Checking nested positivity in the inductive "
                   uu____2889
                  in
               debug_log env uu____2888);
              (let uu____2892 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____2892 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____2905 =
                       FStar_TypeChecker_Env.lookup_attrs_of_lid env ilid  in
                     (match uu____2905 with
                      | FStar_Pervasives_Native.None  ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some [] ->
                          (debug_log env
                             "Checking nested positivity, not an inductive, return false";
                           false)
                      | FStar_Pervasives_Native.Some attrs ->
                          let uu____2921 =
                            FStar_All.pipe_right attrs
                              (FStar_Util.for_some
                                 (fun tm  ->
                                    let uu____2928 =
                                      let uu____2929 =
                                        FStar_Syntax_Subst.compress tm  in
                                      uu____2929.FStar_Syntax_Syntax.n  in
                                    match uu____2928 with
                                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.assume_strictly_positive_attr_lid
                                    | uu____2933 -> false))
                             in
                          if uu____2921
                          then
                            ((let uu____2935 =
                                let uu____2936 =
                                  FStar_Ident.string_of_lid ilid  in
                                FStar_Util.format1
                                  "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                  uu____2936
                                 in
                              debug_log env uu____2935);
                             true)
                          else
                            (debug_log env
                               "Checking nested positivity, not an inductive, return false";
                             false))
                   else
                     (let uu____2940 =
                        already_unfolded ilid args unfolded env  in
                      if uu____2940
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____2964 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____2964  in
                         (let uu____2968 =
                            let uu____2969 =
                              let uu____2970 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2970
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2969
                             in
                          debug_log env uu____2968);
                         (let uu____2972 =
                            let uu____2973 = FStar_ST.op_Bang unfolded  in
                            let uu____3019 =
                              let uu____3026 =
                                let uu____3031 =
                                  let uu____3032 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3032  in
                                (ilid, uu____3031)  in
                              [uu____3026]  in
                            FStar_List.append uu____2973 uu____3019  in
                          FStar_ST.op_Colon_Equals unfolded uu____2972);
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
                  (let uu____3177 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3177 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3199 ->
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
                         (let uu____3202 =
                            let uu____3203 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3203
                             in
                          debug_log env uu____3202);
                         (let uu____3204 =
                            let uu____3205 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3205.FStar_Syntax_Syntax.n  in
                          match uu____3204 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3231 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3231 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3294 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3294 dbs1
                                       in
                                    let c1 =
                                      let uu____3298 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3298 c
                                       in
                                    let uu____3301 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3301 with
                                     | (args1,uu____3335) ->
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
                                           let uu____3427 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3427 c1
                                            in
                                         ((let uu____3437 =
                                             let uu____3438 =
                                               let uu____3439 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3440 =
                                                 let uu____3441 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3441
                                                  in
                                               Prims.strcat uu____3439
                                                 uu____3440
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3438
                                              in
                                           debug_log env uu____3437);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3472 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3474 =
                                  let uu____3475 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3475.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3474
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
                   (let uu____3541 = try_get_fv t1  in
                    match uu____3541 with
                    | (fv,uu____3547) ->
                        let uu____3548 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3548
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3573 =
                      let uu____3574 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3574
                       in
                    debug_log env uu____3573);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3576 =
                      FStar_List.fold_left
                        (fun uu____3595  ->
                           fun b  ->
                             match uu____3595 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3618 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3641 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3618, uu____3641))) (true, env)
                        sbs1
                       in
                    match uu____3576 with | (b,uu____3655) -> b))
              | uu____3656 ->
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
              let uu____3707 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3707 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3729 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3731 =
                      let uu____3732 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3732
                       in
                    debug_log env uu____3731);
                   (let uu____3733 =
                      let uu____3734 = FStar_Syntax_Subst.compress dt  in
                      uu____3734.FStar_Syntax_Syntax.n  in
                    match uu____3733 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3737 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3740) ->
                        let dbs1 =
                          let uu____3770 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3770  in
                        let dbs2 =
                          let uu____3820 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3820 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3825 =
                            let uu____3826 =
                              let uu____3827 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3827 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3826
                             in
                          debug_log env uu____3825);
                         (let uu____3834 =
                            FStar_List.fold_left
                              (fun uu____3853  ->
                                 fun b  ->
                                   match uu____3853 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3876 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3899 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3876, uu____3899)))
                              (true, env) dbs3
                             in
                          match uu____3834 with | (b,uu____3913) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3914,uu____3915) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3968 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3986 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4002,uu____4003,uu____4004) -> (lid, us, bs)
        | uu____4013 -> failwith "Impossible!"  in
      match uu____3986 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4023 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4023 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4046 =
                 let uu____4049 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4049  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4061 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4061
                      unfolded_inductives env2) uu____4046)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4091,uu____4092,t,uu____4094,uu____4095,uu____4096) -> t
    | uu____4101 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4121 =
         let uu____4122 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4122 haseq_suffix  in
       uu____4121 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4142 =
      let uu____4145 =
        let uu____4148 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4148]  in
      FStar_List.append lid.FStar_Ident.ns uu____4145  in
    FStar_Ident.lid_of_ids uu____4142
  
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
          let uu____4193 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4207,bs,t,uu____4210,uu____4211) -> (lid, bs, t)
            | uu____4220 -> failwith "Impossible!"  in
          match uu____4193 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4242 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4242 t  in
              let uu____4251 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4251 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4269 =
                       let uu____4270 = FStar_Syntax_Subst.compress t2  in
                       uu____4270.FStar_Syntax_Syntax.n  in
                     match uu____4269 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4274) -> ibs
                     | uu____4295 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4304 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4305 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4304 uu____4305
                      in
                   let ind1 =
                     let uu____4311 =
                       let uu____4316 =
                         FStar_List.map
                           (fun uu____4333  ->
                              match uu____4333 with
                              | (bv,aq) ->
                                  let uu____4352 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4352, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4316  in
                     uu____4311 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4360 =
                       let uu____4365 =
                         FStar_List.map
                           (fun uu____4382  ->
                              match uu____4382 with
                              | (bv,aq) ->
                                  let uu____4401 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4401, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4365  in
                     uu____4360 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4409 =
                       let uu____4414 =
                         let uu____4415 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4415]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4414
                        in
                     uu____4409 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4466 =
                            let uu____4467 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4467  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4466) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4480 =
                              let uu____4483 =
                                let uu____4488 =
                                  let uu____4489 =
                                    let uu____4498 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4498  in
                                  [uu____4489]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4488
                                 in
                              uu____4483 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4480)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___353_4523 = fml  in
                     let uu____4524 =
                       let uu____4525 =
                         let uu____4532 =
                           let uu____4533 =
                             let uu____4546 =
                               let uu____4557 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4557]  in
                             [uu____4546]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4533  in
                         (fml, uu____4532)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4525  in
                     {
                       FStar_Syntax_Syntax.n = uu____4524;
                       FStar_Syntax_Syntax.pos =
                         (uu___353_4523.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___353_4523.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4612 =
                              let uu____4617 =
                                let uu____4618 =
                                  let uu____4627 =
                                    let uu____4628 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4628 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4627  in
                                [uu____4618]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4617
                               in
                            uu____4612 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4685 =
                              let uu____4690 =
                                let uu____4691 =
                                  let uu____4700 =
                                    let uu____4701 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4701 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4700  in
                                [uu____4691]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4690
                               in
                            uu____4685 FStar_Pervasives_Native.None
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
          let uu____4777 =
            let uu____4778 = FStar_Syntax_Subst.compress dt1  in
            uu____4778.FStar_Syntax_Syntax.n  in
          match uu____4777 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4782) ->
              let dbs1 =
                let uu____4812 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4812  in
              let dbs2 =
                let uu____4862 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4862 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4877 =
                           let uu____4882 =
                             let uu____4883 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4883]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4882
                            in
                         uu____4877 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4916 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4916 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4924 =
                       let uu____4929 =
                         let uu____4930 =
                           let uu____4939 =
                             let uu____4940 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4940
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4939  in
                         [uu____4930]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4929
                        in
                     uu____4924 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4989 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5079,uu____5080,uu____5081,uu____5082,uu____5083)
                  -> lid
              | uu____5092 -> failwith "Impossible!"  in
            let uu____5093 = acc  in
            match uu____5093 with
            | (uu____5130,en,uu____5132,uu____5133) ->
                let uu____5154 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5154 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5191 = acc  in
                     (match uu____5191 with
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
                                     (uu____5265,uu____5266,uu____5267,t_lid,uu____5269,uu____5270)
                                     -> t_lid = lid
                                 | uu____5275 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5288 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5288)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5291 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5294 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5291, uu____5294)))
  
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
          let us =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5353,us,uu____5355,uu____5356,uu____5357,uu____5358)
                -> us
            | uu____5367 -> failwith "Impossible!"  in
          let uu____5368 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____5368 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____5393 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____5393 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____5471 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____5471 with
                     | (phi1,uu____5479) ->
                         ((let uu____5481 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____5481
                           then
                             let uu____5482 =
                               FStar_TypeChecker_Env.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____5482
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____5499  ->
                                    match uu____5499 with
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
                                             FStar_Syntax_Syntax.sigrng =
                                               FStar_Range.dummyRange;
                                             FStar_Syntax_Syntax.sigquals =
                                               [];
                                             FStar_Syntax_Syntax.sigmeta =
                                               FStar_Syntax_Syntax.default_sigmeta;
                                             FStar_Syntax_Syntax.sigattrs =
                                               []
                                           }]) [] axioms
                              in
                           (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
                             "haseq";
                           ses)))))
  
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
                let uu____5567 =
                  let uu____5568 = FStar_Syntax_Subst.compress t  in
                  uu____5568.FStar_Syntax_Syntax.n  in
                match uu____5567 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5575) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5612 = is_mutual t'  in
                    if uu____5612
                    then true
                    else
                      (let uu____5614 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5614)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5634) -> is_mutual t'
                | uu____5639 -> false
              
              and exists_mutual uu___340_5640 =
                match uu___340_5640 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5659 =
                let uu____5660 = FStar_Syntax_Subst.compress dt1  in
                uu____5660.FStar_Syntax_Syntax.n  in
              match uu____5659 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5666) ->
                  let dbs1 =
                    let uu____5696 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5696  in
                  let dbs2 =
                    let uu____5746 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5746 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5766 =
                               let uu____5771 =
                                 let uu____5772 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5772]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5771
                                in
                             uu____5766 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5804 = is_mutual sort  in
                             if uu____5804
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
                           let uu____5816 =
                             let uu____5821 =
                               let uu____5822 =
                                 let uu____5831 =
                                   let uu____5832 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5832 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5831  in
                               [uu____5822]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5821
                              in
                           uu____5816 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5881 -> acc
  
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
              let uu____5930 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5952,bs,t,uu____5955,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5967 -> failwith "Impossible!"  in
              match uu____5930 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5990 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5990 t  in
                  let uu____5999 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5999 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6009 =
                           let uu____6010 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6010.FStar_Syntax_Syntax.n  in
                         match uu____6009 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6014) ->
                             ibs
                         | uu____6035 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6044 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6045 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6044
                           uu____6045
                          in
                       let ind1 =
                         let uu____6051 =
                           let uu____6056 =
                             FStar_List.map
                               (fun uu____6073  ->
                                  match uu____6073 with
                                  | (bv,aq) ->
                                      let uu____6092 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6092, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6056  in
                         uu____6051 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6100 =
                           let uu____6105 =
                             FStar_List.map
                               (fun uu____6122  ->
                                  match uu____6122 with
                                  | (bv,aq) ->
                                      let uu____6141 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6141, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6105  in
                         uu____6100 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6149 =
                           let uu____6154 =
                             let uu____6155 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6155]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6154
                            in
                         uu____6149 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6193,uu____6194,uu____6195,t_lid,uu____6197,uu____6198)
                                  -> t_lid = lid
                              | uu____6203 -> failwith "Impossible")
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
                         let uu___354_6213 = fml  in
                         let uu____6214 =
                           let uu____6215 =
                             let uu____6222 =
                               let uu____6223 =
                                 let uu____6236 =
                                   let uu____6247 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____6247]  in
                                 [uu____6236]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6223
                                in
                             (fml, uu____6222)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6215  in
                         {
                           FStar_Syntax_Syntax.n = uu____6214;
                           FStar_Syntax_Syntax.pos =
                             (uu___354_6213.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___354_6213.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6302 =
                                  let uu____6307 =
                                    let uu____6308 =
                                      let uu____6317 =
                                        let uu____6318 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6318
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6317
                                       in
                                    [uu____6308]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6307
                                   in
                                uu____6302 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6375 =
                                  let uu____6380 =
                                    let uu____6381 =
                                      let uu____6390 =
                                        let uu____6391 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6391
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6390
                                       in
                                    [uu____6381]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6380
                                   in
                                uu____6375 FStar_Pervasives_Native.None
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
                     (lid,uu____6484,uu____6485,uu____6486,uu____6487,uu____6488)
                     -> lid
                 | uu____6497 -> failwith "Impossible!") tcs
             in
          let uu____6498 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6510,uu____6511,uu____6512,uu____6513) ->
                (lid, us)
            | uu____6522 -> failwith "Impossible!"  in
          match uu____6498 with
          | (lid,us) ->
              let uu____6531 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6531 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6558 =
                       let uu____6559 =
                         let uu____6566 = get_haseq_axiom_lid lid  in
                         (uu____6566, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6559  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6558;
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
          let uu____6619 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___341_6644  ->
                    match uu___341_6644 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6645;
                        FStar_Syntax_Syntax.sigrng = uu____6646;
                        FStar_Syntax_Syntax.sigquals = uu____6647;
                        FStar_Syntax_Syntax.sigmeta = uu____6648;
                        FStar_Syntax_Syntax.sigattrs = uu____6649;_} -> true
                    | uu____6670 -> false))
             in
          match uu____6619 with
          | (tys,datas) ->
              ((let uu____6692 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___342_6701  ->
                          match uu___342_6701 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6702;
                              FStar_Syntax_Syntax.sigrng = uu____6703;
                              FStar_Syntax_Syntax.sigquals = uu____6704;
                              FStar_Syntax_Syntax.sigmeta = uu____6705;
                              FStar_Syntax_Syntax.sigattrs = uu____6706;_} ->
                              false
                          | uu____6725 -> true))
                   in
                if uu____6692
                then
                  let uu____6726 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6726
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6734 =
                       let uu____6735 = FStar_List.hd tys  in
                       uu____6735.FStar_Syntax_Syntax.sigel  in
                     match uu____6734 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6738,uvs,uu____6740,uu____6741,uu____6742,uu____6743)
                         -> uvs
                     | uu____6752 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6756 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6782 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6782 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6820,bs,t,l1,l2) ->
                                      let uu____6833 =
                                        let uu____6850 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6851 =
                                          let uu____6852 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6852
                                            t
                                           in
                                        (lid, univs2, uu____6850, uu____6851,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6833
                                  | uu____6865 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___355_6866 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___355_6866.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___355_6866.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___355_6866.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___355_6866.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6876,t,lid_t,x,l) ->
                                      let uu____6885 =
                                        let uu____6900 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6900, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6885
                                  | uu____6903 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___356_6904 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___356_6904.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___356_6904.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___356_6904.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___356_6904.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6905 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6905, tys1, datas1))
                   in
                match uu____6756 with
                | (env1,tys1,datas1) ->
                    let uu____6931 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____6970  ->
                             match uu____6970 with
                             | (env2,all_tcs,g) ->
                                 let uu____7010 = tc_tycon env2 tc  in
                                 (match uu____7010 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____7037 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____7037
                                        then
                                          let uu____7038 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7038
                                        else ());
                                       (let uu____7040 =
                                          let uu____7041 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7041
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7040))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____6931 with
                     | (env2,tcs,g) ->
                         let uu____7087 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____7109  ->
                                  match uu____7109 with
                                  | (datas2,g1) ->
                                      let uu____7128 =
                                        let uu____7133 = tc_data env2 tcs  in
                                        uu____7133 se  in
                                      (match uu____7128 with
                                       | (data,g') ->
                                           let uu____7150 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____7150)))
                             datas1 ([], g)
                            in
                         (match uu____7087 with
                          | (datas2,g1) ->
                              let uu____7171 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7189 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____7189, datas2))
                                 in
                              (match uu____7171 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____7221 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____7222 =
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
                                         uu____7221;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7222
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____7248,uu____7249)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7269 =
                                                    let uu____7274 =
                                                      let uu____7275 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____7276 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7275 uu____7276
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7274)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____7269
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____7277 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____7277 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____7293)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7324 ->
                                                             let uu____7325 =
                                                               let uu____7332
                                                                 =
                                                                 let uu____7333
                                                                   =
                                                                   let uu____7348
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____7348)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7333
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7332
                                                                in
                                                             uu____7325
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
                                                       let uu____7372 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____7372 with
                                                        | (uu____7377,inferred)
                                                            ->
                                                            let uu____7379 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____7379
                                                             with
                                                             | (uu____7384,expected)
                                                                 ->
                                                                 let uu____7386
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____7386
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7389 -> ()));
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
                          let uu____7481 =
                            let uu____7488 =
                              let uu____7489 =
                                let uu____7496 =
                                  let uu____7499 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7499  in
                                (uu____7496, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7489  in
                            FStar_Syntax_Syntax.mk uu____7488  in
                          uu____7481 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7536  ->
                                  match uu____7536 with
                                  | (x,imp) ->
                                      let uu____7555 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7555, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____7559 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7559  in
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
                               let uu____7580 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____7580
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____7581 =
                               let uu____7584 =
                                 let uu____7587 =
                                   let uu____7592 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7593 =
                                     let uu____7594 =
                                       let uu____7603 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7603
                                        in
                                     [uu____7594]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7592
                                     uu____7593
                                    in
                                 uu____7587 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____7584  in
                             FStar_Syntax_Util.refine x uu____7581  in
                           let uu____7630 =
                             let uu___357_7631 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___357_7631.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___357_7631.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7630)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7648 =
                          FStar_List.map
                            (fun uu____7672  ->
                               match uu____7672 with
                               | (x,uu____7686) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____7648 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7745  ->
                                match uu____7745 with
                                | (x,uu____7759) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____7769 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7769)
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
                               (let uu____7782 =
                                  let uu____7783 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7783.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7782)
                              in
                           let quals =
                             let uu____7787 =
                               FStar_List.filter
                                 (fun uu___343_7791  ->
                                    match uu___343_7791 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7792 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7787
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7827 =
                                 let uu____7828 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7828  in
                               FStar_Syntax_Syntax.mk_Total uu____7827  in
                             let uu____7829 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7829
                              in
                           let decl =
                             let uu____7833 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7833;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7835 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7835
                            then
                              let uu____7836 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7836
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
                                             fun uu____7887  ->
                                               match uu____7887 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7911 =
                                                       let uu____7914 =
                                                         let uu____7915 =
                                                           let uu____7922 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7922,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7915
                                                          in
                                                       pos uu____7914  in
                                                     (uu____7911, b)
                                                   else
                                                     (let uu____7928 =
                                                        let uu____7931 =
                                                          let uu____7932 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7932
                                                           in
                                                        pos uu____7931  in
                                                      (uu____7928, b))))
                                      in
                                   let pat_true =
                                     let uu____7950 =
                                       let uu____7953 =
                                         let uu____7954 =
                                           let uu____7967 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____7967, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7954
                                          in
                                       pos uu____7953  in
                                     (uu____7950,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____8001 =
                                       let uu____8004 =
                                         let uu____8005 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8005
                                          in
                                       pos uu____8004  in
                                     (uu____8001,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____8019 =
                                     let uu____8026 =
                                       let uu____8027 =
                                         let uu____8050 =
                                           let uu____8067 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____8082 =
                                             let uu____8099 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____8099]  in
                                           uu____8067 :: uu____8082  in
                                         (arg_exp, uu____8050)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8027
                                        in
                                     FStar_Syntax_Syntax.mk uu____8026  in
                                   uu____8019 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____8178 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____8178
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
                                let uu____8192 =
                                  let uu____8197 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____8197  in
                                let uu____8198 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____8192
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8198 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____8204 =
                                  let uu____8205 =
                                    let uu____8212 =
                                      let uu____8215 =
                                        let uu____8216 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____8216
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____8215]  in
                                    ((false, [lb]), uu____8212)  in
                                  FStar_Syntax_Syntax.Sig_let uu____8205  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8204;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____8228 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____8228
                               then
                                 let uu____8229 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8229
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
                                fun uu____8299  ->
                                  match uu____8299 with
                                  | (a,uu____8307) ->
                                      let uu____8312 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____8312 with
                                       | (field_name,uu____8318) ->
                                           let field_proj_tm =
                                             let uu____8320 =
                                               let uu____8321 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8321
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8320 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____8346 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8388  ->
                                    match uu____8388 with
                                    | (x,uu____8398) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____8404 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____8404 with
                                         | (field_name,uu____8412) ->
                                             let t =
                                               let uu____8416 =
                                                 let uu____8417 =
                                                   let uu____8420 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8420
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8417
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8416
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8425 =
                                                    let uu____8426 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____8426.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8425)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8442 =
                                                   FStar_List.filter
                                                     (fun uu___344_8446  ->
                                                        match uu___344_8446
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8447 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8442
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___345_8460  ->
                                                         match uu___345_8460
                                                         with
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8461 ->
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
                                               let uu____8469 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8469;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____8471 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____8471
                                               then
                                                 let uu____8472 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8472
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
                                                           fun uu____8518  ->
                                                             match uu____8518
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
                                                                   let uu____8542
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____8542,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8558
                                                                    =
                                                                    let uu____8561
                                                                    =
                                                                    let uu____8562
                                                                    =
                                                                    let uu____8569
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8569,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8562
                                                                     in
                                                                    pos
                                                                    uu____8561
                                                                     in
                                                                    (uu____8558,
                                                                    b))
                                                                   else
                                                                    (let uu____8575
                                                                    =
                                                                    let uu____8578
                                                                    =
                                                                    let uu____8579
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8579
                                                                     in
                                                                    pos
                                                                    uu____8578
                                                                     in
                                                                    (uu____8575,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____8597 =
                                                     let uu____8600 =
                                                       let uu____8601 =
                                                         let uu____8614 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____8614,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8601
                                                        in
                                                     pos uu____8600  in
                                                   let uu____8623 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____8597,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8623)
                                                    in
                                                 let body =
                                                   let uu____8639 =
                                                     let uu____8646 =
                                                       let uu____8647 =
                                                         let uu____8670 =
                                                           let uu____8687 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____8687]  in
                                                         (arg_exp,
                                                           uu____8670)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8647
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8646
                                                      in
                                                   uu____8639
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____8755 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____8755
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
                                                   let uu____8766 =
                                                     let uu____8771 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____8771
                                                      in
                                                   let uu____8772 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8766;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8772;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____8778 =
                                                     let uu____8779 =
                                                       let uu____8786 =
                                                         let uu____8789 =
                                                           let uu____8790 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____8790
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____8789]  in
                                                       ((false, [lb]),
                                                         uu____8786)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8779
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8778;
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
                                                 (let uu____8802 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____8802
                                                  then
                                                    let uu____8803 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8803
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____8346 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8851) when
              let uu____8856 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8856 ->
              let uu____8857 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8857 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8879 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8879 with
                    | (formals,uu____8897) ->
                        let uu____8918 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8950 =
                                   let uu____8951 =
                                     let uu____8952 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8952  in
                                   FStar_Ident.lid_equals typ_lid uu____8951
                                    in
                                 if uu____8950
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8971,uvs',tps,typ0,uu____8975,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8992 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9033 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9033
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____8918 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9060 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9060 with
                              | (indices,uu____9078) ->
                                  let refine_domain =
                                    let uu____9100 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___346_9105  ->
                                              match uu___346_9105 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9106 -> true
                                              | uu____9115 -> false))
                                       in
                                    if uu____9100
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___347_9125 =
                                      match uu___347_9125 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9128,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9140 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9141 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9141 with
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
                                    let uu____9152 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9152 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9235  ->
                                               fun uu____9236  ->
                                                 match (uu____9235,
                                                         uu____9236)
                                                 with
                                                 | ((x,uu____9262),(x',uu____9264))
                                                     ->
                                                     let uu____9285 =
                                                       let uu____9292 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9292)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9285) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9297 -> []
  