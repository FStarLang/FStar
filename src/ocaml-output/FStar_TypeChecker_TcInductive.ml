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
                                             (let uu____291 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____291))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____298 =
                                              let uu____304 =
                                                let uu____306 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____308 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____306 uu____308
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____304)
                                               in
                                            FStar_Errors.raise_error
                                              uu____298
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
                                            let uu____321 =
                                              let uu____330 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____347 =
                                                let uu____356 =
                                                  let uu____369 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____369
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____356
                                                 in
                                              FStar_List.append uu____330
                                                uu____347
                                               in
                                            let uu____392 =
                                              let uu____395 =
                                                let uu____396 =
                                                  let uu____401 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____401
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____396
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____395
                                               in
                                            FStar_Syntax_Util.arrow uu____321
                                              uu____392
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____418 =
                                            let uu____423 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____424 =
                                              let uu____425 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____425 k4
                                               in
                                            (uu____423, uu____424)  in
                                          match uu____418 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____445 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____445,
                                                (let uu___61_451 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____456 -> failwith "impossible"
  
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
            let uu____520 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____520 with
             | (usubst,_uvs1) ->
                 let uu____543 =
                   let uu____548 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____549 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____548, uu____549)  in
                 (match uu____543 with
                  | (env1,t1) ->
                      let uu____556 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____595  ->
                               match uu____595 with
                               | (se1,u_tc) ->
                                   let uu____610 =
                                     let uu____612 =
                                       let uu____613 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____613  in
                                     FStar_Ident.lid_equals tc_lid uu____612
                                      in
                                   if uu____610
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____633,uu____634,tps,uu____636,uu____637,uu____638)
                                          ->
                                          let tps1 =
                                            let uu____648 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____648
                                              (FStar_List.map
                                                 (fun uu____688  ->
                                                    match uu____688 with
                                                    | (x,uu____702) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____710 =
                                            let uu____717 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____717, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____710
                                      | uu____724 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____767 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____767
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____556 with
                       | (env2,tps,u_tc) ->
                           let uu____799 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____815 =
                               let uu____816 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____816.FStar_Syntax_Syntax.n  in
                             match uu____815 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____855 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____855 with
                                  | (uu____896,bs') ->
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
                                                fun uu____967  ->
                                                  match uu____967 with
                                                  | (x,uu____976) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____983 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____983)
                             | uu____984 -> ([], t2)  in
                           (match uu____799 with
                            | (arguments,result) ->
                                ((let uu____1028 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____1028
                                  then
                                    let uu____1031 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____1033 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____1036 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1031 uu____1033 uu____1036
                                  else ());
                                 (let uu____1041 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____1041 with
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
                                      let uu____1059 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____1059 with
                                       | (result1,res_lcomp) ->
                                           let uu____1070 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____1070 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____1128 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1128
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____1210  ->
                                                      fun uu____1211  ->
                                                        match (uu____1210,
                                                                uu____1211)
                                                        with
                                                        | ((bv,uu____1241),
                                                           (t2,uu____1243))
                                                            ->
                                                            let uu____1270 =
                                                              let uu____1271
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____1271.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____1270
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1275 ->
                                                                 let uu____1276
                                                                   =
                                                                   let uu____1282
                                                                    =
                                                                    let uu____1284
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____1286
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1284
                                                                    uu____1286
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1282)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____1276
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1291 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1291
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____1293 =
                                                     let uu____1294 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____1294.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1293 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1297 -> ()
                                                   | uu____1298 ->
                                                       let uu____1299 =
                                                         let uu____1305 =
                                                           let uu____1307 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____1309 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1307
                                                             uu____1309
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1305)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1299
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1314 =
                                                       let uu____1315 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____1315.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____1314 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1319;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1320;_},tuvs)
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
                                                                    let uu____1334
                                                                    =
                                                                    let uu____1335
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1336
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
                                                                    uu____1335
                                                                    uu____1336
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1334)
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
                                                     | uu____1342 ->
                                                         let uu____1343 =
                                                           let uu____1349 =
                                                             let uu____1351 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____1353 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1351
                                                               uu____1353
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1349)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____1343
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____1371  ->
                                                            fun u_x  ->
                                                              match uu____1371
                                                              with
                                                              | (x,uu____1380)
                                                                  ->
                                                                  let uu____1385
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1385)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____1389 =
                                                       let uu____1398 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1438
                                                                  ->
                                                                 match uu____1438
                                                                 with
                                                                 | (x,uu____1452)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____1398
                                                         arguments1
                                                        in
                                                     let uu____1466 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1389 uu____1466
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___183_1471 = se
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
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____1475 -> failwith "impossible"
  
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
          let binders =
            FStar_All.pipe_right tcs
              (FStar_List.map
                 (fun uu____1571  ->
                    match uu____1571 with
                    | (se,uu____1577) ->
                        (match se.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (uu____1578,uu____1579,tps,k,uu____1582,uu____1583)
                             ->
                             let uu____1592 =
                               let uu____1593 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               FStar_All.pipe_left
                                 (FStar_Syntax_Util.arrow tps) uu____1593
                                in
                             FStar_Syntax_Syntax.null_binder uu____1592
                         | uu____1598 -> failwith "Impossible")))
             in
          let binders' =
            FStar_All.pipe_right datas
              (FStar_List.map
                 (fun se  ->
                    match se.FStar_Syntax_Syntax.sigel with
                    | FStar_Syntax_Syntax.Sig_datacon
                        (uu____1627,uu____1628,t,uu____1630,uu____1631,uu____1632)
                        -> FStar_Syntax_Syntax.null_binder t
                    | uu____1639 -> failwith "Impossible"))
             in
          let t =
            let uu____1644 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
            FStar_Syntax_Util.arrow (FStar_List.append binders binders')
              uu____1644
             in
          (let uu____1654 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1654
           then
             let uu____1659 =
               FStar_TypeChecker_Normalize.term_to_string env t  in
             FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
               uu____1659
           else ());
          (let uu____1664 = FStar_TypeChecker_Util.generalize_universes env t
              in
           match uu____1664 with
           | (uvs,t1) ->
               ((let uu____1684 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "GenUniverses")
                    in
                 if uu____1684
                 then
                   let uu____1689 =
                     let uu____1691 =
                       FStar_All.pipe_right uvs
                         (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                        in
                     FStar_All.pipe_right uu____1691
                       (FStar_String.concat ", ")
                      in
                   let uu____1708 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                     uu____1689 uu____1708
                 else ());
                (let uu____1713 = FStar_Syntax_Subst.open_univ_vars uvs t1
                    in
                 match uu____1713 with
                 | (uvs1,t2) ->
                     let uu____1728 = FStar_Syntax_Util.arrow_formals t2  in
                     (match uu____1728 with
                      | (args,uu____1752) ->
                          let uu____1773 =
                            FStar_Util.first_N (FStar_List.length binders)
                              args
                             in
                          (match uu____1773 with
                           | (tc_types,data_types) ->
                               let tcs1 =
                                 FStar_List.map2
                                   (fun uu____1878  ->
                                      fun uu____1879  ->
                                        match (uu____1878, uu____1879) with
                                        | ((x,uu____1901),(se,uu____1903)) ->
                                            (match se.FStar_Syntax_Syntax.sigel
                                             with
                                             | FStar_Syntax_Syntax.Sig_inductive_typ
                                                 (tc,uu____1919,tps,uu____1921,mutuals,datas1)
                                                 ->
                                                 let ty =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs1
                                                     x.FStar_Syntax_Syntax.sort
                                                    in
                                                 let uu____1933 =
                                                   let uu____1938 =
                                                     let uu____1939 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____1939.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1938 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (binders1,c) ->
                                                       let uu____1968 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              tps) binders1
                                                          in
                                                       (match uu____1968 with
                                                        | (tps1,rest) ->
                                                            let t3 =
                                                              match rest with
                                                              | [] ->
                                                                  FStar_Syntax_Util.comp_result
                                                                    c
                                                              | uu____2046 ->
                                                                  FStar_Syntax_Syntax.mk
                                                                    (
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                               in
                                                            (tps1, t3))
                                                   | uu____2065 -> ([], ty)
                                                    in
                                                 (match uu____1933 with
                                                  | (tps1,t3) ->
                                                      let uu___261_2074 = se
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.sigel
                                                          =
                                                          (FStar_Syntax_Syntax.Sig_inductive_typ
                                                             (tc, uvs1, tps1,
                                                               t3, mutuals,
                                                               datas1));
                                                        FStar_Syntax_Syntax.sigrng
                                                          =
                                                          (uu___261_2074.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___261_2074.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___261_2074.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___261_2074.FStar_Syntax_Syntax.sigattrs)
                                                      })
                                             | uu____2079 ->
                                                 failwith "Impossible"))
                                   tc_types tcs
                                  in
                               let datas1 =
                                 match uvs1 with
                                 | [] -> datas
                                 | uu____2086 ->
                                     let uvs_universes =
                                       FStar_All.pipe_right uvs1
                                         (FStar_List.map
                                            (fun _2090  ->
                                               FStar_Syntax_Syntax.U_name
                                                 _2090))
                                        in
                                     let tc_insts =
                                       FStar_All.pipe_right tcs1
                                         (FStar_List.map
                                            (fun uu___0_2109  ->
                                               match uu___0_2109 with
                                               | {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     FStar_Syntax_Syntax.Sig_inductive_typ
                                                     (tc,uu____2115,uu____2116,uu____2117,uu____2118,uu____2119);
                                                   FStar_Syntax_Syntax.sigrng
                                                     = uu____2120;
                                                   FStar_Syntax_Syntax.sigquals
                                                     = uu____2121;
                                                   FStar_Syntax_Syntax.sigmeta
                                                     = uu____2122;
                                                   FStar_Syntax_Syntax.sigattrs
                                                     = uu____2123;_}
                                                   -> (tc, uvs_universes)
                                               | uu____2136 ->
                                                   failwith "Impossible"))
                                        in
                                     FStar_List.map2
                                       (fun uu____2160  ->
                                          fun d  ->
                                            match uu____2160 with
                                            | (t3,uu____2169) ->
                                                (match d.FStar_Syntax_Syntax.sigel
                                                 with
                                                 | FStar_Syntax_Syntax.Sig_datacon
                                                     (l,uu____2175,uu____2176,tc,ntps,mutuals)
                                                     ->
                                                     let ty =
                                                       let uu____2187 =
                                                         FStar_Syntax_InstFV.instantiate
                                                           tc_insts
                                                           t3.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2187
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            uvs1)
                                                        in
                                                     let uu___297_2188 = d
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         =
                                                         (FStar_Syntax_Syntax.Sig_datacon
                                                            (l, uvs1, ty, tc,
                                                              ntps, mutuals));
                                                       FStar_Syntax_Syntax.sigrng
                                                         =
                                                         (uu___297_2188.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___297_2188.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___297_2188.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___297_2188.FStar_Syntax_Syntax.sigattrs)
                                                     }
                                                 | uu____2192 ->
                                                     failwith "Impossible"))
                                       data_types datas
                                  in
                               (tcs1, datas1))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____2211 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2211
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2233 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2233
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____2250 =
      let uu____2251 = FStar_Syntax_Subst.compress t  in
      uu____2251.FStar_Syntax_Syntax.n  in
    match uu____2250 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2270 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2276 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____2313 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2362  ->
               match uu____2362 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2406 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2406  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2313
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2611 =
             let uu____2613 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____2613
              in
           debug_log env uu____2611);
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
           (let uu____2618 =
              let uu____2620 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____2620
               in
            debug_log env uu____2618);
           (let uu____2625 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2625) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2638 =
                  let uu____2639 = FStar_Syntax_Subst.compress btype1  in
                  uu____2639.FStar_Syntax_Syntax.n  in
                match uu____2638 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2669 = try_get_fv t  in
                    (match uu____2669 with
                     | (fv,us) ->
                         let uu____2677 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2677
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2693  ->
                                 match uu____2693 with
                                 | (t1,uu____2702) ->
                                     let uu____2707 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2707) args)
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
                          let uu____2742 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2742
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2746 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2746
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
                            (fun uu____2773  ->
                               match uu____2773 with
                               | (b,uu____2782) ->
                                   let uu____2787 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2787) sbs)
                           &&
                           ((let uu____2793 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2793 with
                             | (uu____2799,return_type) ->
                                 let uu____2801 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2801)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2802 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2806 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2811) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2819) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2826,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2885  ->
                          match uu____2885 with
                          | (p,uu____2898,t) ->
                              let bs =
                                let uu____2917 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2917
                                 in
                              let uu____2926 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2926 with
                               | (bs1,t1) ->
                                   let uu____2934 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2934)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2936,uu____2937)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2980 ->
                    ((let uu____2982 =
                        let uu____2984 =
                          let uu____2986 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2988 =
                            let uu____2990 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____2990  in
                          Prims.op_Hat uu____2986 uu____2988  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____2984
                         in
                      debug_log env uu____2982);
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
              (let uu____3003 =
                 let uu____3005 =
                   let uu____3007 =
                     let uu____3009 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____3009  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____3007  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____3005
                  in
               debug_log env uu____3003);
              (let uu____3013 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3013 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3032 =
                       let uu____3034 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3034
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____3032
                      then
                        ((let uu____3038 =
                            let uu____3040 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____3040
                             in
                          debug_log env uu____3038);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____3051 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3051
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____3062 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3062  in
                         (let uu____3068 =
                            let uu____3070 =
                              let uu____3072 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____3072
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____3070
                             in
                          debug_log env uu____3068);
                         (let uu____3077 =
                            let uu____3078 = FStar_ST.op_Bang unfolded  in
                            let uu____3104 =
                              let uu____3111 =
                                let uu____3116 =
                                  let uu____3117 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3117  in
                                (ilid, uu____3116)  in
                              [uu____3111]  in
                            FStar_List.append uu____3078 uu____3104  in
                          FStar_ST.op_Colon_Equals unfolded uu____3077);
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
                  (let uu____3216 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3216 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3239 ->
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
                         (let uu____3243 =
                            let uu____3245 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____3245
                             in
                          debug_log env uu____3243);
                         (let uu____3248 =
                            let uu____3249 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3249.FStar_Syntax_Syntax.n  in
                          match uu____3248 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3277 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3277 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3341 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3341 dbs1
                                       in
                                    let c1 =
                                      let uu____3345 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3345 c
                                       in
                                    let uu____3348 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3348 with
                                     | (args1,uu____3383) ->
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
                                           let uu____3475 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3475 c1
                                            in
                                         ((let uu____3485 =
                                             let uu____3487 =
                                               let uu____3489 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3492 =
                                                 let uu____3494 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____3494
                                                  in
                                               Prims.op_Hat uu____3489
                                                 uu____3492
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3487
                                              in
                                           debug_log env uu____3485);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3508 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3511 =
                                  let uu____3512 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3512.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3511
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
                   (let uu____3551 = try_get_fv t1  in
                    match uu____3551 with
                    | (fv,uu____3558) ->
                        let uu____3559 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3559
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3591 =
                      let uu____3593 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3593
                       in
                    debug_log env uu____3591);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3598 =
                      FStar_List.fold_left
                        (fun uu____3619  ->
                           fun b  ->
                             match uu____3619 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3650 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3654 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3650, uu____3654))) (true, env)
                        sbs1
                       in
                    match uu____3598 with | (b,uu____3672) -> b))
              | uu____3675 ->
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
              let uu____3711 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3711 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3734 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3737 =
                      let uu____3739 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____3739
                       in
                    debug_log env uu____3737);
                   (let uu____3742 =
                      let uu____3743 = FStar_Syntax_Subst.compress dt  in
                      uu____3743.FStar_Syntax_Syntax.n  in
                    match uu____3742 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3747 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3752) ->
                        let dbs1 =
                          let uu____3782 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3782  in
                        let dbs2 =
                          let uu____3832 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3832 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3837 =
                            let uu____3839 =
                              let uu____3841 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____3841 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3839
                             in
                          debug_log env uu____3837);
                         (let uu____3851 =
                            FStar_List.fold_left
                              (fun uu____3872  ->
                                 fun b  ->
                                   match uu____3872 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3903 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3907 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3903, uu____3907)))
                              (true, env) dbs3
                             in
                          match uu____3851 with | (b,uu____3925) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3928,uu____3929) ->
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
      let uu____3988 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4004,uu____4005,uu____4006) -> (lid, us, bs)
        | uu____4015 -> failwith "Impossible!"  in
      match uu____3988 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4027 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4027 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4051 =
                 let uu____4054 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4054  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4068 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4068
                      unfolded_inductives env2) uu____4051)
  
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
        (uu____4103,uu____4104,t,uu____4106,uu____4107,uu____4108) -> t
    | uu____4115 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4132 =
         let uu____4134 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4134 haseq_suffix  in
       uu____4132 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4144 =
      let uu____4147 =
        let uu____4150 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4150]  in
      FStar_List.append lid.FStar_Ident.ns uu____4147  in
    FStar_Ident.lid_of_ids uu____4144
  
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
          let uu____4196 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4210,bs,t,uu____4213,uu____4214) -> (lid, bs, t)
            | uu____4223 -> failwith "Impossible!"  in
          match uu____4196 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4246 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4246 t  in
              let uu____4255 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4255 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4273 =
                       let uu____4274 = FStar_Syntax_Subst.compress t2  in
                       uu____4274.FStar_Syntax_Syntax.n  in
                     match uu____4273 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4278) -> ibs
                     | uu____4299 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4308 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4309 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4308 uu____4309
                      in
                   let ind1 =
                     let uu____4315 =
                       let uu____4320 =
                         FStar_List.map
                           (fun uu____4337  ->
                              match uu____4337 with
                              | (bv,aq) ->
                                  let uu____4356 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4356, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4320  in
                     uu____4315 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4362 =
                       let uu____4367 =
                         FStar_List.map
                           (fun uu____4384  ->
                              match uu____4384 with
                              | (bv,aq) ->
                                  let uu____4403 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4403, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4367  in
                     uu____4362 FStar_Pervasives_Native.None
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
                          let uu____4464 =
                            let uu____4465 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4465  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4464) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4478 =
                              let uu____4481 =
                                let uu____4486 =
                                  let uu____4487 =
                                    let uu____4496 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4496  in
                                  [uu____4487]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4486
                                 in
                              uu____4481 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4478)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___631_4519 = fml  in
                     let uu____4520 =
                       let uu____4521 =
                         let uu____4528 =
                           let uu____4529 =
                             let uu____4550 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____4555 =
                               let uu____4568 =
                                 let uu____4579 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____4579]  in
                               [uu____4568]  in
                             (uu____4550, uu____4555)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4529  in
                         (fml, uu____4528)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4521  in
                     {
                       FStar_Syntax_Syntax.n = uu____4520;
                       FStar_Syntax_Syntax.pos =
                         (uu___631_4519.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___631_4519.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4648 =
                              let uu____4653 =
                                let uu____4654 =
                                  let uu____4663 =
                                    let uu____4664 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4664 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4663  in
                                [uu____4654]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4653
                               in
                            uu____4648 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4717 =
                              let uu____4722 =
                                let uu____4723 =
                                  let uu____4732 =
                                    let uu____4733 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4733 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4732  in
                                [uu____4723]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4722
                               in
                            uu____4717 FStar_Pervasives_Native.None
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
                         let uu____4945 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4945 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4953 =
                       let uu____4958 =
                         let uu____4959 =
                           let uu____4968 =
                             let uu____4969 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4969
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4968  in
                         [uu____4959]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4958
                        in
                     uu____4953 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5016 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5107,uu____5108,uu____5109,uu____5110,uu____5111)
                  -> lid
              | uu____5120 -> failwith "Impossible!"  in
            let uu____5122 = acc  in
            match uu____5122 with
            | (uu____5159,en,uu____5161,uu____5162) ->
                let uu____5183 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5183 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5220 = acc  in
                     (match uu____5220 with
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
                                     (uu____5295,uu____5296,uu____5297,t_lid,uu____5299,uu____5300)
                                     -> t_lid = lid
                                 | uu____5307 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5322 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5322)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5325 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5328 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5325, uu____5328)))
  
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
          let uu____5386 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5396,us,uu____5398,t,uu____5400,uu____5401) -> 
                (us, t)
            | uu____5410 -> failwith "Impossible!"  in
          match uu____5386 with
          | (us,t) ->
              let uu____5420 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5420 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5446 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5446 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5524 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5524 with
                           | (uu____5539,t1) ->
                               let uu____5561 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5561
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5566 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5566 with
                          | (phi1,uu____5574) ->
                              ((let uu____5576 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5576
                                then
                                  let uu____5579 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5579
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5597  ->
                                         match uu____5597 with
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
                let uu____5669 =
                  let uu____5670 = FStar_Syntax_Subst.compress t  in
                  uu____5670.FStar_Syntax_Syntax.n  in
                match uu____5669 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5678) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5715 = is_mutual t'  in
                    if uu____5715
                    then true
                    else
                      (let uu____5722 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5722)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5742) -> is_mutual t'
                | uu____5747 -> false
              
              and exists_mutual uu___1_5749 =
                match uu___1_5749 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5770 =
                let uu____5771 = FStar_Syntax_Subst.compress dt1  in
                uu____5771.FStar_Syntax_Syntax.n  in
              match uu____5770 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5777) ->
                  let dbs1 =
                    let uu____5807 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5807  in
                  let dbs2 =
                    let uu____5857 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5857 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5877 =
                               let uu____5882 =
                                 let uu____5883 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5883]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5882
                                in
                             uu____5877 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5913 = is_mutual sort  in
                             if uu____5913
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
                           let uu____5926 =
                             let uu____5931 =
                               let uu____5932 =
                                 let uu____5941 =
                                   let uu____5942 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5942 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5941  in
                               [uu____5932]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5931
                              in
                           uu____5926 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5989 -> acc
  
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
              let uu____6039 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6061,bs,t,uu____6064,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6076 -> failwith "Impossible!"  in
              match uu____6039 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6100 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6100 t  in
                  let uu____6109 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6109 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6119 =
                           let uu____6120 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6120.FStar_Syntax_Syntax.n  in
                         match uu____6119 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6124) ->
                             ibs
                         | uu____6145 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6154 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6155 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6154
                           uu____6155
                          in
                       let ind1 =
                         let uu____6161 =
                           let uu____6166 =
                             FStar_List.map
                               (fun uu____6183  ->
                                  match uu____6183 with
                                  | (bv,aq) ->
                                      let uu____6202 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6202, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6166  in
                         uu____6161 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6208 =
                           let uu____6213 =
                             FStar_List.map
                               (fun uu____6230  ->
                                  match uu____6230 with
                                  | (bv,aq) ->
                                      let uu____6249 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6249, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6213  in
                         uu____6208 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6255 =
                           let uu____6260 =
                             let uu____6261 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6261]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6260
                            in
                         uu____6255 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6298,uu____6299,uu____6300,t_lid,uu____6302,uu____6303)
                                  -> t_lid = lid
                              | uu____6310 -> failwith "Impossible")
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
                         let uu___868_6322 = fml  in
                         let uu____6323 =
                           let uu____6324 =
                             let uu____6331 =
                               let uu____6332 =
                                 let uu____6353 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____6358 =
                                   let uu____6371 =
                                     let uu____6382 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____6382]  in
                                   [uu____6371]  in
                                 (uu____6353, uu____6358)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6332
                                in
                             (fml, uu____6331)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6324  in
                         {
                           FStar_Syntax_Syntax.n = uu____6323;
                           FStar_Syntax_Syntax.pos =
                             (uu___868_6322.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___868_6322.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6451 =
                                  let uu____6456 =
                                    let uu____6457 =
                                      let uu____6466 =
                                        let uu____6467 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6467
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6466
                                       in
                                    [uu____6457]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6456
                                   in
                                uu____6451 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6520 =
                                  let uu____6525 =
                                    let uu____6526 =
                                      let uu____6535 =
                                        let uu____6536 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6536
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6535
                                       in
                                    [uu____6526]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6525
                                   in
                                uu____6520 FStar_Pervasives_Native.None
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
                     (lid,uu____6628,uu____6629,uu____6630,uu____6631,uu____6632)
                     -> lid
                 | uu____6641 -> failwith "Impossible!") tcs
             in
          let uu____6643 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6655,uu____6656,uu____6657,uu____6658) ->
                (lid, us)
            | uu____6667 -> failwith "Impossible!"  in
          match uu____6643 with
          | (lid,us) ->
              let uu____6677 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6677 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6704 =
                       let uu____6705 =
                         let uu____6712 = get_haseq_axiom_lid lid  in
                         (uu____6712, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6705  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6704;
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
          let uu____6766 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6791  ->
                    match uu___2_6791 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6793;
                        FStar_Syntax_Syntax.sigrng = uu____6794;
                        FStar_Syntax_Syntax.sigquals = uu____6795;
                        FStar_Syntax_Syntax.sigmeta = uu____6796;
                        FStar_Syntax_Syntax.sigattrs = uu____6797;_} -> true
                    | uu____6819 -> false))
             in
          match uu____6766 with
          | (tys,datas) ->
              ((let uu____6842 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6853  ->
                          match uu___3_6853 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6855;
                              FStar_Syntax_Syntax.sigrng = uu____6856;
                              FStar_Syntax_Syntax.sigquals = uu____6857;
                              FStar_Syntax_Syntax.sigmeta = uu____6858;
                              FStar_Syntax_Syntax.sigattrs = uu____6859;_} ->
                              false
                          | uu____6880 -> true))
                   in
                if uu____6842
                then
                  let uu____6883 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6883
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6898 =
                       let uu____6899 = FStar_List.hd tys  in
                       uu____6899.FStar_Syntax_Syntax.sigel  in
                     match uu____6898 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6902,uvs,uu____6904,uu____6905,uu____6906,uu____6907)
                         -> uvs
                     | uu____6916 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6921 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6951 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6951 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____6989,bs,t,l1,l2) ->
                                      let uu____7002 =
                                        let uu____7019 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____7020 =
                                          let uu____7021 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____7021
                                            t
                                           in
                                        (lid, univs2, uu____7019, uu____7020,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____7002
                                  | uu____7034 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___964_7036 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___964_7036.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___964_7036.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___964_7036.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___964_7036.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____7046,t,lid_t,x,l) ->
                                      let uu____7057 =
                                        let uu____7073 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____7073, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____7057
                                  | uu____7077 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___978_7079 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___978_7079.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___978_7079.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___978_7079.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___978_7079.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____7080 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____7080, tys1, datas1))
                   in
                match uu____6921 with
                | (env1,tys1,datas1) ->
                    let uu____7106 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____7145  ->
                             match uu____7145 with
                             | (env2,all_tcs,g) ->
                                 let uu____7185 = tc_tycon env2 tc  in
                                 (match uu____7185 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____7212 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____7212
                                        then
                                          let uu____7215 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7215
                                        else ());
                                       (let uu____7220 =
                                          let uu____7221 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7221
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7220))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____7106 with
                     | (env2,tcs,g) ->
                         let uu____7267 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____7289  ->
                                  match uu____7289 with
                                  | (datas2,g1) ->
                                      let uu____7308 =
                                        let uu____7313 = tc_data env2 tcs  in
                                        uu____7313 se  in
                                      (match uu____7308 with
                                       | (data,g') ->
                                           let uu____7330 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____7330)))
                             datas1 ([], g)
                            in
                         (match uu____7267 with
                          | (datas2,g1) ->
                              let uu____7351 =
                                let tc_universe_vars =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    tcs
                                   in
                                let g2 =
                                  let uu___1013_7368 = g1  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      (uu___1013_7368.FStar_TypeChecker_Env.guard_f);
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___1013_7368.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (tc_universe_vars,
                                        (FStar_Pervasives_Native.snd
                                           g1.FStar_TypeChecker_Env.univ_ineqs));
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___1013_7368.FStar_TypeChecker_Env.implicits)
                                  }  in
                                (let uu____7378 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "GenUniverses")
                                    in
                                 if uu____7378
                                 then
                                   let uu____7383 =
                                     FStar_TypeChecker_Rel.guard_to_string
                                       env2 g2
                                      in
                                   FStar_Util.print1
                                     "@@@@@@Guard before (possible) generalization: %s\n"
                                     uu____7383
                                 else ());
                                FStar_TypeChecker_Rel.force_trivial_guard
                                  env2 g2;
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g2 tcs
                                    datas2
                                else
                                  (let uu____7402 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____7402, datas2))
                                 in
                              (match uu____7351 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____7434 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____7435 =
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
                                         uu____7434;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7435
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____7461,uu____7462)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7482 =
                                                    let uu____7488 =
                                                      let uu____7490 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____7492 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7490 uu____7492
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7488)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____7482
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____7496 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____7496 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____7512)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7543 ->
                                                             let uu____7544 =
                                                               let uu____7551
                                                                 =
                                                                 let uu____7552
                                                                   =
                                                                   let uu____7567
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____7567)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7552
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7551
                                                                in
                                                             uu____7544
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
                                                       let uu____7589 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____7589 with
                                                        | (uu____7594,inferred)
                                                            ->
                                                            let uu____7596 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____7596
                                                             with
                                                             | (uu____7601,expected)
                                                                 ->
                                                                 let uu____7603
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____7603
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7610 -> ()));
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
                          let uu____7721 =
                            let uu____7728 =
                              let uu____7729 =
                                let uu____7736 =
                                  let uu____7739 =
                                    FStar_Syntax_Syntax.lid_as_fv tc
                                      FStar_Syntax_Syntax.delta_constant
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.fv_to_tm uu____7739  in
                                (uu____7736, inst_univs)  in
                              FStar_Syntax_Syntax.Tm_uinst uu____7729  in
                            FStar_Syntax_Syntax.mk uu____7728  in
                          uu____7721 FStar_Pervasives_Native.None p  in
                        let args =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7773  ->
                                  match uu____7773 with
                                  | (x,imp) ->
                                      let uu____7792 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      (uu____7792, imp)))
                           in
                        FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                          FStar_Pervasives_Native.None p
                         in
                      let unrefined_arg_binder =
                        let uu____7796 = projectee arg_typ  in
                        FStar_Syntax_Syntax.mk_binder uu____7796  in
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
                               let uu____7819 =
                                 FStar_Ident.set_lid_range disc_name p  in
                               FStar_Syntax_Syntax.fvar uu____7819
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1"))
                                 FStar_Pervasives_Native.None
                                in
                             let uu____7821 =
                               let uu____7824 =
                                 let uu____7827 =
                                   let uu____7832 =
                                     FStar_Syntax_Syntax.mk_Tm_uinst
                                       disc_fvar inst_univs
                                      in
                                   let uu____7833 =
                                     let uu____7834 =
                                       let uu____7843 =
                                         FStar_Syntax_Syntax.bv_to_name x  in
                                       FStar_All.pipe_left
                                         FStar_Syntax_Syntax.as_arg
                                         uu____7843
                                        in
                                     [uu____7834]  in
                                   FStar_Syntax_Syntax.mk_Tm_app uu____7832
                                     uu____7833
                                    in
                                 uu____7827 FStar_Pervasives_Native.None p
                                  in
                               FStar_Syntax_Util.b2t uu____7824  in
                             FStar_Syntax_Util.refine x uu____7821  in
                           let uu____7868 =
                             let uu___1086_7869 = projectee arg_typ  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1086_7869.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1086_7869.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = sort
                             }  in
                           FStar_Syntax_Syntax.mk_binder uu____7868)
                         in
                      let ntps = FStar_List.length tps  in
                      let all_params =
                        let uu____7886 =
                          FStar_List.map
                            (fun uu____7910  ->
                               match uu____7910 with
                               | (x,uu____7924) ->
                                   (x,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.imp_tag))) tps
                           in
                        FStar_List.append uu____7886 fields  in
                      let imp_binders =
                        FStar_All.pipe_right (FStar_List.append tps indices)
                          (FStar_List.map
                             (fun uu____7983  ->
                                match uu____7983 with
                                | (x,uu____7997) ->
                                    (x,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))))
                         in
                      let early_prims_inductive =
                        (let uu____8008 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid
                           uu____8008)
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
                               (let uu____8029 =
                                  let uu____8031 =
                                    FStar_TypeChecker_Env.current_module env
                                     in
                                  uu____8031.FStar_Ident.str  in
                                FStar_Options.dont_gen_projectors uu____8029)
                              in
                           let quals =
                             let uu____8035 =
                               FStar_List.filter
                                 (fun uu___4_8039  ->
                                    match uu___4_8039 with
                                    | FStar_Syntax_Syntax.Abstract  ->
                                        Prims.op_Negation only_decl
                                    | FStar_Syntax_Syntax.Inline_for_extraction
                                         -> true
                                    | FStar_Syntax_Syntax.NoExtract  -> true
                                    | FStar_Syntax_Syntax.Private  -> true
                                    | uu____8044 -> false) iquals
                                in
                             FStar_List.append
                               ((FStar_Syntax_Syntax.Discriminator lid) ::
                               (if only_decl
                                then
                                  [FStar_Syntax_Syntax.Logic;
                                  FStar_Syntax_Syntax.Assumption]
                                else [])) uu____8035
                              in
                           let binders =
                             FStar_List.append imp_binders
                               [unrefined_arg_binder]
                              in
                           let t =
                             let bool_typ =
                               let uu____8082 =
                                 let uu____8083 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.bool_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.fv_to_tm uu____8083  in
                               FStar_Syntax_Syntax.mk_Total uu____8082  in
                             let uu____8084 =
                               FStar_Syntax_Util.arrow binders bool_typ  in
                             FStar_All.pipe_left
                               (FStar_Syntax_Subst.close_univ_vars uvs)
                               uu____8084
                              in
                           let decl =
                             let uu____8088 =
                               FStar_Ident.range_of_lid discriminator_name
                                in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (discriminator_name, uvs, t));
                               FStar_Syntax_Syntax.sigrng = uu____8088;
                               FStar_Syntax_Syntax.sigquals = quals;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = []
                             }  in
                           (let uu____8090 =
                              FStar_TypeChecker_Env.debug env
                                (FStar_Options.Other "LogTypes")
                               in
                            if uu____8090
                            then
                              let uu____8094 =
                                FStar_Syntax_Print.sigelt_to_string decl  in
                              FStar_Util.print1
                                "Declaration of a discriminator %s\n"
                                uu____8094
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
                                             fun uu____8155  ->
                                               match uu____8155 with
                                               | (x,imp) ->
                                                   let b =
                                                     FStar_Syntax_Syntax.is_implicit
                                                       imp
                                                      in
                                                   if b && (j < ntps)
                                                   then
                                                     let uu____8180 =
                                                       let uu____8183 =
                                                         let uu____8184 =
                                                           let uu____8191 =
                                                             FStar_Syntax_Syntax.gen_bv
                                                               (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                               FStar_Pervasives_Native.None
                                                               FStar_Syntax_Syntax.tun
                                                              in
                                                           (uu____8191,
                                                             FStar_Syntax_Syntax.tun)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_dot_term
                                                           uu____8184
                                                          in
                                                       pos uu____8183  in
                                                     (uu____8180, b)
                                                   else
                                                     (let uu____8199 =
                                                        let uu____8202 =
                                                          let uu____8203 =
                                                            FStar_Syntax_Syntax.gen_bv
                                                              (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                              FStar_Pervasives_Native.None
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          FStar_Syntax_Syntax.Pat_wild
                                                            uu____8203
                                                           in
                                                        pos uu____8202  in
                                                      (uu____8199, b))))
                                      in
                                   let pat_true =
                                     let uu____8222 =
                                       let uu____8225 =
                                         let uu____8226 =
                                           let uu____8240 =
                                             FStar_Syntax_Syntax.lid_as_fv
                                               lid
                                               FStar_Syntax_Syntax.delta_constant
                                               (FStar_Pervasives_Native.Some
                                                  fvq)
                                              in
                                           (uu____8240, arg_pats)  in
                                         FStar_Syntax_Syntax.Pat_cons
                                           uu____8226
                                          in
                                       pos uu____8225  in
                                     (uu____8222,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_true_bool)
                                      in
                                   let pat_false =
                                     let uu____8275 =
                                       let uu____8278 =
                                         let uu____8279 =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             FStar_Syntax_Syntax.tun
                                            in
                                         FStar_Syntax_Syntax.Pat_wild
                                           uu____8279
                                          in
                                       pos uu____8278  in
                                     (uu____8275,
                                       FStar_Pervasives_Native.None,
                                       FStar_Syntax_Util.exp_false_bool)
                                      in
                                   let arg_exp =
                                     FStar_Syntax_Syntax.bv_to_name
                                       (FStar_Pervasives_Native.fst
                                          unrefined_arg_binder)
                                      in
                                   let uu____8293 =
                                     let uu____8300 =
                                       let uu____8301 =
                                         let uu____8324 =
                                           let uu____8341 =
                                             FStar_Syntax_Util.branch
                                               pat_true
                                              in
                                           let uu____8356 =
                                             let uu____8373 =
                                               FStar_Syntax_Util.branch
                                                 pat_false
                                                in
                                             [uu____8373]  in
                                           uu____8341 :: uu____8356  in
                                         (arg_exp, uu____8324)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____8301
                                        in
                                     FStar_Syntax_Syntax.mk uu____8300  in
                                   uu____8293 FStar_Pervasives_Native.None p)
                                 in
                              let dd =
                                let uu____8449 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Syntax_Syntax.Abstract)
                                   in
                                if uu____8449
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
                                let uu____8471 =
                                  let uu____8476 =
                                    FStar_Syntax_Syntax.lid_as_fv
                                      discriminator_name dd
                                      FStar_Pervasives_Native.None
                                     in
                                  FStar_Util.Inr uu____8476  in
                                let uu____8477 =
                                  FStar_Syntax_Subst.close_univ_vars uvs imp
                                   in
                                FStar_Syntax_Util.mk_letbinding uu____8471
                                  uvs lbtyp FStar_Parser_Const.effect_Tot_lid
                                  uu____8477 [] FStar_Range.dummyRange
                                 in
                              let impl =
                                let uu____8483 =
                                  let uu____8484 =
                                    let uu____8491 =
                                      let uu____8494 =
                                        let uu____8495 =
                                          FStar_All.pipe_right
                                            lb.FStar_Syntax_Syntax.lbname
                                            FStar_Util.right
                                           in
                                        FStar_All.pipe_right uu____8495
                                          (fun fv  ->
                                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                         in
                                      [uu____8494]  in
                                    ((false, [lb]), uu____8491)  in
                                  FStar_Syntax_Syntax.Sig_let uu____8484  in
                                {
                                  FStar_Syntax_Syntax.sigel = uu____8483;
                                  FStar_Syntax_Syntax.sigrng = p;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = []
                                }  in
                              (let uu____8509 =
                                 FStar_TypeChecker_Env.debug env
                                   (FStar_Options.Other "LogTypes")
                                  in
                               if uu____8509
                               then
                                 let uu____8513 =
                                   FStar_Syntax_Print.sigelt_to_string impl
                                    in
                                 FStar_Util.print1
                                   "Implementation of a discriminator %s\n"
                                   uu____8513
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
                                fun uu____8586  ->
                                  match uu____8586 with
                                  | (a,uu____8595) ->
                                      let uu____8600 =
                                        FStar_Syntax_Util.mk_field_projector_name
                                          lid a i
                                         in
                                      (match uu____8600 with
                                       | (field_name,uu____8606) ->
                                           let field_proj_tm =
                                             let uu____8608 =
                                               let uu____8609 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   field_name
                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                      (Prims.parse_int "1"))
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.fv_to_tm
                                                 uu____8609
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_uinst
                                               uu____8608 inst_univs
                                              in
                                           let proj =
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               field_proj_tm [arg]
                                               FStar_Pervasives_Native.None p
                                              in
                                           FStar_Syntax_Syntax.NT (a, proj))))
                         in
                      let projectors_ses =
                        let uu____8635 =
                          FStar_All.pipe_right fields
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____8677  ->
                                    match uu____8677 with
                                    | (x,uu____8688) ->
                                        let p1 =
                                          FStar_Syntax_Syntax.range_of_bv x
                                           in
                                        let uu____8694 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid x i
                                           in
                                        (match uu____8694 with
                                         | (field_name,uu____8702) ->
                                             let t =
                                               let uu____8706 =
                                                 let uu____8707 =
                                                   let uu____8710 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total
                                                     uu____8710
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   binders uu____8707
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Syntax_Subst.close_univ_vars
                                                    uvs) uu____8706
                                                in
                                             let only_decl =
                                               early_prims_inductive ||
                                                 (let uu____8716 =
                                                    let uu____8718 =
                                                      FStar_TypeChecker_Env.current_module
                                                        env
                                                       in
                                                    uu____8718.FStar_Ident.str
                                                     in
                                                  FStar_Options.dont_gen_projectors
                                                    uu____8716)
                                                in
                                             let no_decl = false  in
                                             let quals q =
                                               if only_decl
                                               then
                                                 let uu____8737 =
                                                   FStar_List.filter
                                                     (fun uu___5_8741  ->
                                                        match uu___5_8741
                                                        with
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> false
                                                        | uu____8744 -> true)
                                                     q
                                                    in
                                                 FStar_Syntax_Syntax.Assumption
                                                   :: uu____8737
                                               else q  in
                                             let quals1 =
                                               let iquals1 =
                                                 FStar_All.pipe_right iquals
                                                   (FStar_List.filter
                                                      (fun uu___6_8759  ->
                                                         match uu___6_8759
                                                         with
                                                         | FStar_Syntax_Syntax.Inline_for_extraction
                                                              -> true
                                                         | FStar_Syntax_Syntax.NoExtract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Abstract
                                                              -> true
                                                         | FStar_Syntax_Syntax.Private
                                                              -> true
                                                         | uu____8765 ->
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
                                               let uu____8776 =
                                                 FStar_Ident.range_of_lid
                                                   field_name
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.sigel =
                                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                                      (field_name, uvs, t));
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____8776;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = quals1;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   =
                                                   FStar_Syntax_Syntax.default_sigmeta;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = attrs
                                               }  in
                                             ((let uu____8778 =
                                                 FStar_TypeChecker_Env.debug
                                                   env
                                                   (FStar_Options.Other
                                                      "LogTypes")
                                                  in
                                               if uu____8778
                                               then
                                                 let uu____8782 =
                                                   FStar_Syntax_Print.sigelt_to_string
                                                     decl
                                                    in
                                                 FStar_Util.print1
                                                   "Declaration of a projector %s\n"
                                                   uu____8782
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
                                                           fun uu____8836  ->
                                                             match uu____8836
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
                                                                   let uu____8862
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                   (uu____8862,
                                                                    b)
                                                                 else
                                                                   if
                                                                    b &&
                                                                    (j < ntps)
                                                                   then
                                                                    (let uu____8878
                                                                    =
                                                                    let uu____8881
                                                                    =
                                                                    let uu____8882
                                                                    =
                                                                    let uu____8889
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8889,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8882
                                                                     in
                                                                    pos
                                                                    uu____8881
                                                                     in
                                                                    (uu____8878,
                                                                    b))
                                                                   else
                                                                    (let uu____8897
                                                                    =
                                                                    let uu____8900
                                                                    =
                                                                    let uu____8901
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8901
                                                                     in
                                                                    pos
                                                                    uu____8900
                                                                     in
                                                                    (uu____8897,
                                                                    b))))
                                                    in
                                                 let pat =
                                                   let uu____8920 =
                                                     let uu____8923 =
                                                       let uu____8924 =
                                                         let uu____8938 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             (FStar_Pervasives_Native.Some
                                                                fvq)
                                                            in
                                                         (uu____8938,
                                                           arg_pats)
                                                          in
                                                       FStar_Syntax_Syntax.Pat_cons
                                                         uu____8924
                                                        in
                                                     pos uu____8923  in
                                                   let uu____8948 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       projection
                                                      in
                                                   (uu____8920,
                                                     FStar_Pervasives_Native.None,
                                                     uu____8948)
                                                    in
                                                 let body =
                                                   let uu____8964 =
                                                     let uu____8971 =
                                                       let uu____8972 =
                                                         let uu____8995 =
                                                           let uu____9012 =
                                                             FStar_Syntax_Util.branch
                                                               pat
                                                              in
                                                           [uu____9012]  in
                                                         (arg_exp,
                                                           uu____8995)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_match
                                                         uu____8972
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____8971
                                                      in
                                                   uu____8964
                                                     FStar_Pervasives_Native.None
                                                     p1
                                                    in
                                                 let imp =
                                                   FStar_Syntax_Util.abs
                                                     binders body
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 let dd =
                                                   let uu____9077 =
                                                     FStar_All.pipe_right
                                                       quals1
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.Abstract)
                                                      in
                                                   if uu____9077
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
                                                   let uu____9096 =
                                                     let uu____9101 =
                                                       FStar_Syntax_Syntax.lid_as_fv
                                                         field_name dd
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     FStar_Util.Inr
                                                       uu____9101
                                                      in
                                                   let uu____9102 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs imp
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.lbname
                                                       = uu____9096;
                                                     FStar_Syntax_Syntax.lbunivs
                                                       = uvs;
                                                     FStar_Syntax_Syntax.lbtyp
                                                       = lbtyp;
                                                     FStar_Syntax_Syntax.lbeff
                                                       =
                                                       FStar_Parser_Const.effect_Tot_lid;
                                                     FStar_Syntax_Syntax.lbdef
                                                       = uu____9102;
                                                     FStar_Syntax_Syntax.lbattrs
                                                       = [];
                                                     FStar_Syntax_Syntax.lbpos
                                                       =
                                                       FStar_Range.dummyRange
                                                   }  in
                                                 let impl =
                                                   let uu____9108 =
                                                     let uu____9109 =
                                                       let uu____9116 =
                                                         let uu____9119 =
                                                           let uu____9120 =
                                                             FStar_All.pipe_right
                                                               lb.FStar_Syntax_Syntax.lbname
                                                               FStar_Util.right
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____9120
                                                             (fun fv  ->
                                                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                            in
                                                         [uu____9119]  in
                                                       ((false, [lb]),
                                                         uu____9116)
                                                        in
                                                     FStar_Syntax_Syntax.Sig_let
                                                       uu____9109
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       = uu____9108;
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
                                                 (let uu____9134 =
                                                    FStar_TypeChecker_Env.debug
                                                      env
                                                      (FStar_Options.Other
                                                         "LogTypes")
                                                     in
                                                  if uu____9134
                                                  then
                                                    let uu____9138 =
                                                      FStar_Syntax_Print.sigelt_to_string
                                                        impl
                                                       in
                                                    FStar_Util.print1
                                                      "Implementation of a projector %s\n"
                                                      uu____9138
                                                  else ());
                                                 if no_decl
                                                 then [impl]
                                                 else [decl; impl])))))
                           in
                        FStar_All.pipe_right uu____8635 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____9192) when
              let uu____9199 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____9199 ->
              let uu____9201 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9201 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____9223 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____9223 with
                    | (formals,uu____9241) ->
                        let uu____9262 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____9297 =
                                   let uu____9299 =
                                     let uu____9300 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____9300  in
                                   FStar_Ident.lid_equals typ_lid uu____9299
                                    in
                                 if uu____9297
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9322,uvs',tps,typ0,uu____9326,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____9346 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9395 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9395
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____9262 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9433 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9433 with
                              | (indices,uu____9451) ->
                                  let refine_domain =
                                    let uu____9474 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___7_9481  ->
                                              match uu___7_9481 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9483 -> true
                                              | uu____9493 -> false))
                                       in
                                    if uu____9474
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___8_9508 =
                                      match uu___8_9508 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9511,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9523 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9524 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9524 with
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
                                    let uu____9537 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9537 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9620  ->
                                               fun uu____9621  ->
                                                 match (uu____9620,
                                                         uu____9621)
                                                 with
                                                 | ((x,uu____9647),(x',uu____9649))
                                                     ->
                                                     let uu____9670 =
                                                       let uu____9677 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9677)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9670) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9682 -> []
  