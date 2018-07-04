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
                           FStar_TypeChecker_Env.num_inductive_ty_params env
                             ilid
                            in
                         (let uu____2965 =
                            let uu____2966 =
                              let uu____2967 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.strcat uu____2967
                                ", also adding to the memo table"
                               in
                            Prims.strcat
                              "Checking nested positivity, number of type parameters is "
                              uu____2966
                             in
                          debug_log env uu____2965);
                         (let uu____2969 =
                            let uu____2970 = FStar_ST.op_Bang unfolded  in
                            let uu____3016 =
                              let uu____3023 =
                                let uu____3028 =
                                  let uu____3029 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3029  in
                                (ilid, uu____3028)  in
                              [uu____3023]  in
                            FStar_List.append uu____2970 uu____3016  in
                          FStar_ST.op_Colon_Equals unfolded uu____2969);
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
                  (let uu____3174 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3174 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3196 ->
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
                         (let uu____3199 =
                            let uu____3200 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.strcat
                              "Checking nested positivity in the data constructor type: "
                              uu____3200
                             in
                          debug_log env uu____3199);
                         (let uu____3201 =
                            let uu____3202 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3202.FStar_Syntax_Syntax.n  in
                          match uu____3201 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3228 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3228 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3291 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3291 dbs1
                                       in
                                    let c1 =
                                      let uu____3295 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3295 c
                                       in
                                    let uu____3298 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3298 with
                                     | (args1,uu____3332) ->
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
                                           let uu____3424 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3424 c1
                                            in
                                         ((let uu____3434 =
                                             let uu____3435 =
                                               let uu____3436 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3437 =
                                                 let uu____3438 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.strcat ", and c: "
                                                   uu____3438
                                                  in
                                               Prims.strcat uu____3436
                                                 uu____3437
                                                in
                                             Prims.strcat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3435
                                              in
                                           debug_log env uu____3434);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3469 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3471 =
                                  let uu____3472 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3472.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3471
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
                   (let uu____3538 = try_get_fv t1  in
                    match uu____3538 with
                    | (fv,uu____3544) ->
                        let uu____3545 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3545
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3570 =
                      let uu____3571 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.strcat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3571
                       in
                    debug_log env uu____3570);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3573 =
                      FStar_List.fold_left
                        (fun uu____3592  ->
                           fun b  ->
                             match uu____3592 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3615 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3638 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3615, uu____3638))) (true, env)
                        sbs1
                       in
                    match uu____3573 with | (b,uu____3652) -> b))
              | uu____3653 ->
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
              let uu____3704 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3704 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3726 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3728 =
                      let uu____3729 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.strcat "Checking data constructor type: "
                        uu____3729
                       in
                    debug_log env uu____3728);
                   (let uu____3730 =
                      let uu____3731 = FStar_Syntax_Subst.compress dt  in
                      uu____3731.FStar_Syntax_Syntax.n  in
                    match uu____3730 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3734 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3737) ->
                        let dbs1 =
                          let uu____3767 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3767  in
                        let dbs2 =
                          let uu____3817 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3817 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3822 =
                            let uu____3823 =
                              let uu____3824 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.strcat uu____3824 " binders"  in
                            Prims.strcat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3823
                             in
                          debug_log env uu____3822);
                         (let uu____3831 =
                            FStar_List.fold_left
                              (fun uu____3850  ->
                                 fun b  ->
                                   match uu____3850 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3873 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3896 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3873, uu____3896)))
                              (true, env) dbs3
                             in
                          match uu____3831 with | (b,uu____3910) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3911,uu____3912) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3965 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3983 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____3999,uu____4000,uu____4001) -> (lid, us, bs)
        | uu____4010 -> failwith "Impossible!"  in
      match uu____3983 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4020 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4020 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4043 =
                 let uu____4046 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4046  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4058 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4058
                      unfolded_inductives env2) uu____4043)
  
let (datacon_typ : FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.term) =
  fun data  ->
    match data.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_datacon
        (uu____4088,uu____4089,t,uu____4091,uu____4092,uu____4093) -> t
    | uu____4098 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4118 =
         let uu____4119 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4119 haseq_suffix  in
       uu____4118 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4139 =
      let uu____4142 =
        let uu____4145 =
          FStar_Ident.id_of_text
            (Prims.strcat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4145]  in
      FStar_List.append lid.FStar_Ident.ns uu____4142  in
    FStar_Ident.lid_of_ids uu____4139
  
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
          let uu____4190 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4204,bs,t,uu____4207,uu____4208) -> (lid, bs, t)
            | uu____4217 -> failwith "Impossible!"  in
          match uu____4190 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4239 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4239 t  in
              let uu____4248 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4248 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4266 =
                       let uu____4267 = FStar_Syntax_Subst.compress t2  in
                       uu____4267.FStar_Syntax_Syntax.n  in
                     match uu____4266 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4271) -> ibs
                     | uu____4292 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4301 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4302 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4301 uu____4302
                      in
                   let ind1 =
                     let uu____4308 =
                       let uu____4313 =
                         FStar_List.map
                           (fun uu____4330  ->
                              match uu____4330 with
                              | (bv,aq) ->
                                  let uu____4349 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4349, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4313  in
                     uu____4308 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4357 =
                       let uu____4362 =
                         FStar_List.map
                           (fun uu____4379  ->
                              match uu____4379 with
                              | (bv,aq) ->
                                  let uu____4398 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4398, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4362  in
                     uu____4357 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4406 =
                       let uu____4411 =
                         let uu____4412 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4412]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4411
                        in
                     uu____4406 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4463 =
                            let uu____4464 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4464  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4463) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4477 =
                              let uu____4480 =
                                let uu____4485 =
                                  let uu____4486 =
                                    let uu____4495 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4495  in
                                  [uu____4486]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4485
                                 in
                              uu____4480 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4477)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___353_4520 = fml  in
                     let uu____4521 =
                       let uu____4522 =
                         let uu____4529 =
                           let uu____4530 =
                             let uu____4543 =
                               let uu____4554 =
                                 FStar_Syntax_Syntax.as_arg haseq_ind  in
                               [uu____4554]  in
                             [uu____4543]  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4530  in
                         (fml, uu____4529)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4522  in
                     {
                       FStar_Syntax_Syntax.n = uu____4521;
                       FStar_Syntax_Syntax.pos =
                         (uu___353_4520.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___353_4520.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4609 =
                              let uu____4614 =
                                let uu____4615 =
                                  let uu____4624 =
                                    let uu____4625 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4625 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4624  in
                                [uu____4615]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4614
                               in
                            uu____4609 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4682 =
                              let uu____4687 =
                                let uu____4688 =
                                  let uu____4697 =
                                    let uu____4698 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4698 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4697  in
                                [uu____4688]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4687
                               in
                            uu____4682 FStar_Pervasives_Native.None
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
          let uu____4774 =
            let uu____4775 = FStar_Syntax_Subst.compress dt1  in
            uu____4775.FStar_Syntax_Syntax.n  in
          match uu____4774 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4779) ->
              let dbs1 =
                let uu____4809 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4809  in
              let dbs2 =
                let uu____4859 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4859 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4874 =
                           let uu____4879 =
                             let uu____4880 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4880]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4879
                            in
                         uu____4874 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4913 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4913 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4921 =
                       let uu____4926 =
                         let uu____4927 =
                           let uu____4936 =
                             let uu____4937 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4937
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4936  in
                         [uu____4927]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4926
                        in
                     uu____4921 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____4986 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5076,uu____5077,uu____5078,uu____5079,uu____5080)
                  -> lid
              | uu____5089 -> failwith "Impossible!"  in
            let uu____5090 = acc  in
            match uu____5090 with
            | (uu____5127,en,uu____5129,uu____5130) ->
                let uu____5151 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5151 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5188 = acc  in
                     (match uu____5188 with
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
                                     (uu____5262,uu____5263,uu____5264,t_lid,uu____5266,uu____5267)
                                     -> t_lid = lid
                                 | uu____5272 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5285 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5285)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5288 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5291 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5288, uu____5291)))
  
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
                (uu____5350,us,uu____5352,uu____5353,uu____5354,uu____5355)
                -> us
            | uu____5364 -> failwith "Impossible!"  in
          let uu____5365 = FStar_Syntax_Subst.univ_var_opening us  in
          match uu____5365 with
          | (usubst,us1) ->
              let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle  in
              ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                 "haseq";
               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                 env sig_bndle;
               (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1  in
                let uu____5390 =
                  FStar_List.fold_left (optimized_haseq_ty datas usubst us1)
                    ([], env1, FStar_Syntax_Util.t_true,
                      FStar_Syntax_Util.t_true) tcs
                   in
                match uu____5390 with
                | (axioms,env2,guard,cond) ->
                    let phi = FStar_Syntax_Util.mk_imp guard cond  in
                    let uu____5468 =
                      FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi  in
                    (match uu____5468 with
                     | (phi1,uu____5476) ->
                         ((let uu____5478 =
                             FStar_TypeChecker_Env.should_verify env2  in
                           if uu____5478
                           then
                             let uu____5479 =
                               FStar_TypeChecker_Env.guard_of_guard_formula
                                 (FStar_TypeChecker_Common.NonTrivial phi1)
                                in
                             FStar_TypeChecker_Rel.force_trivial_guard env2
                               uu____5479
                           else ());
                          (let ses =
                             FStar_List.fold_left
                               (fun l  ->
                                  fun uu____5496  ->
                                    match uu____5496 with
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
                let uu____5564 =
                  let uu____5565 = FStar_Syntax_Subst.compress t  in
                  uu____5565.FStar_Syntax_Syntax.n  in
                match uu____5564 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5572) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5609 = is_mutual t'  in
                    if uu____5609
                    then true
                    else
                      (let uu____5611 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5611)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5631) -> is_mutual t'
                | uu____5636 -> false
              
              and exists_mutual uu___340_5637 =
                match uu___340_5637 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5656 =
                let uu____5657 = FStar_Syntax_Subst.compress dt1  in
                uu____5657.FStar_Syntax_Syntax.n  in
              match uu____5656 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5663) ->
                  let dbs1 =
                    let uu____5693 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5693  in
                  let dbs2 =
                    let uu____5743 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5743 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5763 =
                               let uu____5768 =
                                 let uu____5769 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5769]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5768
                                in
                             uu____5763 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5801 = is_mutual sort  in
                             if uu____5801
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
                           let uu____5813 =
                             let uu____5818 =
                               let uu____5819 =
                                 let uu____5828 =
                                   let uu____5829 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5829 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5828  in
                               [uu____5819]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5818
                              in
                           uu____5813 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5878 -> acc
  
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
              let uu____5927 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____5949,bs,t,uu____5952,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____5964 -> failwith "Impossible!"  in
              match uu____5927 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____5987 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____5987 t  in
                  let uu____5996 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____5996 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6006 =
                           let uu____6007 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6007.FStar_Syntax_Syntax.n  in
                         match uu____6006 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6011) ->
                             ibs
                         | uu____6032 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6041 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6042 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6041
                           uu____6042
                          in
                       let ind1 =
                         let uu____6048 =
                           let uu____6053 =
                             FStar_List.map
                               (fun uu____6070  ->
                                  match uu____6070 with
                                  | (bv,aq) ->
                                      let uu____6089 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6089, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6053  in
                         uu____6048 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6097 =
                           let uu____6102 =
                             FStar_List.map
                               (fun uu____6119  ->
                                  match uu____6119 with
                                  | (bv,aq) ->
                                      let uu____6138 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6138, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6102  in
                         uu____6097 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6146 =
                           let uu____6151 =
                             let uu____6152 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6152]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6151
                            in
                         uu____6146 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6190,uu____6191,uu____6192,t_lid,uu____6194,uu____6195)
                                  -> t_lid = lid
                              | uu____6200 -> failwith "Impossible")
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
                         let uu___354_6210 = fml  in
                         let uu____6211 =
                           let uu____6212 =
                             let uu____6219 =
                               let uu____6220 =
                                 let uu____6233 =
                                   let uu____6244 =
                                     FStar_Syntax_Syntax.as_arg haseq_ind  in
                                   [uu____6244]  in
                                 [uu____6233]  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6220
                                in
                             (fml, uu____6219)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6212  in
                         {
                           FStar_Syntax_Syntax.n = uu____6211;
                           FStar_Syntax_Syntax.pos =
                             (uu___354_6210.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___354_6210.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6299 =
                                  let uu____6304 =
                                    let uu____6305 =
                                      let uu____6314 =
                                        let uu____6315 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6315
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6314
                                       in
                                    [uu____6305]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6304
                                   in
                                uu____6299 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6372 =
                                  let uu____6377 =
                                    let uu____6378 =
                                      let uu____6387 =
                                        let uu____6388 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6388
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6387
                                       in
                                    [uu____6378]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6377
                                   in
                                uu____6372 FStar_Pervasives_Native.None
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
                     (lid,uu____6481,uu____6482,uu____6483,uu____6484,uu____6485)
                     -> lid
                 | uu____6494 -> failwith "Impossible!") tcs
             in
          let uu____6495 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6507,uu____6508,uu____6509,uu____6510) ->
                (lid, us)
            | uu____6519 -> failwith "Impossible!"  in
          match uu____6495 with
          | (lid,us) ->
              let uu____6528 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6528 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6555 =
                       let uu____6556 =
                         let uu____6563 = get_haseq_axiom_lid lid  in
                         (uu____6563, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6556  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6555;
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
          let uu____6616 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___341_6641  ->
                    match uu___341_6641 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6642;
                        FStar_Syntax_Syntax.sigrng = uu____6643;
                        FStar_Syntax_Syntax.sigquals = uu____6644;
                        FStar_Syntax_Syntax.sigmeta = uu____6645;
                        FStar_Syntax_Syntax.sigattrs = uu____6646;_} -> true
                    | uu____6667 -> false))
             in
          match uu____6616 with
          | (tys,datas) ->
              ((let uu____6689 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___342_6698  ->
                          match uu___342_6698 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6699;
                              FStar_Syntax_Syntax.sigrng = uu____6700;
                              FStar_Syntax_Syntax.sigquals = uu____6701;
                              FStar_Syntax_Syntax.sigmeta = uu____6702;
                              FStar_Syntax_Syntax.sigattrs = uu____6703;_} ->
                              false
                          | uu____6722 -> true))
                   in
                if uu____6689
                then
                  let uu____6723 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6723
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6731 =
                       let uu____6732 = FStar_List.hd tys  in
                       uu____6732.FStar_Syntax_Syntax.sigel  in
                     match uu____6731 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6735,uvs,uu____6737,uu____6738,uu____6739,uu____6740)
                         -> uvs
                     | uu____6749 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6753 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6779 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6779 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6817,bs,t,l1,l2) ->
                                      let uu____6830 =
                                        let uu____6847 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____6848 =
                                          let uu____6849 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____6849
                                            t
                                           in
                                        (lid, univs2, uu____6847, uu____6848,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____6830
                                  | uu____6862 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___355_6863 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___355_6863.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___355_6863.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___355_6863.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___355_6863.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____6873,t,lid_t,x,l) ->
                                      let uu____6882 =
                                        let uu____6897 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____6897, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____6882
                                  | uu____6900 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___356_6901 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___356_6901.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___356_6901.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___356_6901.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___356_6901.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____6902 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____6902, tys1, datas1))
                   in
                match uu____6753 with
                | (env1,tys1,datas1) ->
                    let uu____6928 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____6967  ->
                             match uu____6967 with
                             | (env2,all_tcs,g) ->
                                 let uu____7007 = tc_tycon env2 tc  in
                                 (match uu____7007 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____7034 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____7034
                                        then
                                          let uu____7035 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7035
                                        else ());
                                       (let uu____7037 =
                                          let uu____7038 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7038
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7037))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____6928 with
                     | (env2,tcs,g) ->
                         let uu____7084 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____7106  ->
                                  match uu____7106 with
                                  | (datas2,g1) ->
                                      let uu____7125 =
                                        let uu____7130 = tc_data env2 tcs  in
                                        uu____7130 se  in
                                      (match uu____7125 with
                                       | (data,g') ->
                                           let uu____7147 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____7147)))
                             datas1 ([], g)
                            in
                         (match uu____7084 with
                          | (datas2,g1) ->
                              let uu____7168 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7186 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____7186, datas2))
                                 in
                              (match uu____7168 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____7218 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____7219 =
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
                                         uu____7218;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7219
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____7245,uu____7246)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7266 =
                                                    let uu____7271 =
                                                      let uu____7272 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____7273 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7272 uu____7273
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7271)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____7266
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____7274 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____7274 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____7290)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7321 ->
                                                             let uu____7322 =
                                                               let uu____7329
                                                                 =
                                                                 let uu____7330
                                                                   =
                                                                   let uu____7345
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____7345)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7330
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7329
                                                                in
                                                             uu____7322
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
                                                       let uu____7369 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____7369 with
                                                        | (uu____7374,inferred)
                                                            ->
                                                            let uu____7376 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____7376
                                                             with
                                                             | (uu____7381,expected)
                                                                 ->
                                                                 let uu____7383
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____7383
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7386 -> ()));
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
                          let uu____7478 =
                            let uu____7485 =
                              let uu____7486 =
                                let uu____7493 =
                                  let uu____7496 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7496  in
                                (uu____7493, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7486  in
                            FStar_Syntax_Syntax.mk uu____7485  in
                          uu____7478 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7533  ->
                                  match uu____7533 with
                                  | (x,imp) ->
                                      let uu____7552 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7552, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____7556 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7556  in
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
                               let uu____7577 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____7577
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____7578 =
                               let uu____7581 =
                                 let uu____7584 =
                                   let uu____7589 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7590 =
                                     let uu____7591 =
                                       let uu____7600 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7600
                                        in
                                     [uu____7591]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7589
                                     uu____7590
                                    in
                                 uu____7584 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____7581  in
                             FStar_Syntax_Util.refine x uu____7578  in
                           let uu____7627 =
                             let uu___357_7628 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___357_7628.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___357_7628.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7627)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7645 =
                          FStar_List.map
                            (fun uu____7669  ->
                               match uu____7669 with
                               | (x,uu____7683) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____7645 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7742  ->
                                match uu____7742 with
                                | (x,uu____7756) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____7766 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____7766)
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
                               (let uu____7779 =
                                  let uu____7780 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____7780.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____7779)
                              in
                           let quals =
                             let uu____7784 =
                               FStar_List.filter
                                 (fun uu___343_7788  ->
                                    match uu___343_7788 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____7789 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____7784
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____7824 =
                                 let uu____7825 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____7825  in
                               FStar_Syntax_Syntax.mk_Total uu____7824  in
                             let uu____7826 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____7826
                              in
                           let decl =
                             let uu____7830 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____7830;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____7832 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____7832
                            then
                              let uu____7833 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____7833
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
                                             fun uu____7884  ->
                                               match uu____7884 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____7908 =
                                                       let uu____7911 =
                                                         let uu____7912 =
                                                           let uu____7919 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____7919,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____7912
                                                          in
                                                       pos uu____7911  in
                                                     (uu____7908, b)
                                                   else
                                                     (let uu____7925 =
                                                        let uu____7928 =
                                                          let uu____7929 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____7929
                                                           in
                                                        pos uu____7928  in
                                                      (uu____7925, b))))
                                      in
                                   let pat_true =
                                     let uu____7947 =
                                       let uu____7950 =
                                         let uu____7951 =
                                           let uu____7964 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____7964, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____7951
                                          in
                                       pos uu____7950  in
                                     (uu____7947,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____7998 =
                                       let uu____8001 =
                                         let uu____8002 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8002
                                          in
                                       pos uu____8001  in
                                     (uu____7998,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____8016 =
                                     let uu____8023 =
                                       let uu____8024 =
                                         let uu____8047 =
                                           let uu____8064 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____8079 =
                                             let uu____8096 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____8096]  in
                                           uu____8064 :: uu____8079  in
                                         (arg_exp, uu____8047)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8024
                                        in
                                     FStar_Syntax_Syntax.mk uu____8023  in
                                   uu____8016 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____8175 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____8175
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
                                let uu____8189 =
                                  let uu____8194 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____8194  in
                                let uu____8195 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____8189
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8195 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____8201 =
                                  let uu____8202 =
                                    let uu____8209 =
                                      let uu____8212 =
                                        let uu____8213 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____8213
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____8212]  in
                                    ((false, [lb]), uu____8209)  in
                                  FStar_Syntax_Syntax.Sig_let uu____8202  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8201;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____8225 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____8225
                               then
                                 let uu____8226 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8226
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
                                fun uu____8296  ->
                                  match uu____8296 with
                                  | (a,uu____8304) ->
                                      let uu____8309 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____8309 with
                                       | (field_name,uu____8315) ->
                                           let field_proj_tm =
                                             let uu____8317 =
                                               let uu____8318 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8318
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8317 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____8343 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8385  ->
                                    match uu____8385 with
                                    | (x,uu____8395) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____8401 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____8401 with
                                         | (field_name,uu____8409) ->
                                             let t =
                                               let uu____8413 =
                                                 let uu____8414 =
                                                   let uu____8417 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8417
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8414
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8413
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8422 =
                                                    let uu____8423 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____8423.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8422)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8439 =
                                                   FStar_List.filter
                                                     (fun uu___344_8443  ->
                                                        match uu___344_8443
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8444 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8439
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___345_8457  ->
                                                         match uu___345_8457
                                                         with
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8458 ->
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
                                               let uu____8466 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8466;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____8468 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____8468
                                               then
                                                 let uu____8469 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8469
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
                                                           fun uu____8515  ->
                                                             match uu____8515
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
                                                                   let uu____8539
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____8539,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8555
                                                                    =
                                                                    let uu____8558
                                                                    =
                                                                    let uu____8559
                                                                    =
                                                                    let uu____8566
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8566,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8559
                                                                     in
                                                                    pos
                                                                    uu____8558
                                                                     in
                                                                    (uu____8555,
                                                                    b))
                                                                   else
                                                                    (let uu____8572
                                                                    =
                                                                    let uu____8575
                                                                    =
                                                                    let uu____8576
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8576
                                                                     in
                                                                    pos
                                                                    uu____8575
                                                                     in
                                                                    (uu____8572,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____8594 =
                                                     let uu____8597 =
                                                       let uu____8598 =
                                                         let uu____8611 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____8611,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8598
                                                        in
                                                     pos uu____8597  in
                                                   let uu____8620 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____8594,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8620)
                                                    in
                                                 let body =
                                                   let uu____8636 =
                                                     let uu____8643 =
                                                       let uu____8644 =
                                                         let uu____8667 =
                                                           let uu____8684 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____8684]  in
                                                         (arg_exp,
                                                           uu____8667)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8644
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8643
                                                      in
                                                   uu____8636
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____8752 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____8752
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
                                                   let uu____8763 =
                                                     let uu____8768 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____8768
                                                      in
                                                   let uu____8769 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____8763;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____8769;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____8775 =
                                                     let uu____8776 =
                                                       let uu____8783 =
                                                         let uu____8786 =
                                                           let uu____8787 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____8787
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____8786]  in
                                                       ((false, [lb]),
                                                         uu____8783)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____8776
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____8775;
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
                                                 (let uu____8799 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____8799
                                                  then
                                                    let uu____8800 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____8800
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____8343 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____8848) when
              let uu____8853 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____8853 ->
              let uu____8854 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____8854 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____8876 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____8876 with
                    | (formals,uu____8894) ->
                        let uu____8915 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____8947 =
                                   let uu____8948 =
                                     let uu____8949 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____8949  in
                                   FStar_Ident.lid_equals typ_lid uu____8948
                                    in
                                 if uu____8947
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____8968,uvs',tps,typ0,uu____8972,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____8989 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9030 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9030
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____8915 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9057 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9057 with
                              | (indices,uu____9075) ->
                                  let refine_domain =
                                    let uu____9097 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___346_9102  ->
                                              match uu___346_9102 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9103 -> true
                                              | uu____9112 -> false))
                                       in
                                    if uu____9097
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___347_9122 =
                                      match uu___347_9122 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9125,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9137 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9138 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9138 with
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
                                    let uu____9149 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9149 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9232  ->
                                               fun uu____9233  ->
                                                 match (uu____9232,
                                                         uu____9233)
                                                 with
                                                 | ((x,uu____9259),(x',uu____9261))
                                                     ->
                                                     let uu____9282 =
                                                       let uu____9289 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9289)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9282) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9294 -> []
  