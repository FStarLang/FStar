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
                                                     (uu___61_451.FStar_Syntax_Syntax.sigattrs);
                                                   FStar_Syntax_Syntax.sigopts
                                                     =
                                                     (uu___61_451.FStar_Syntax_Syntax.sigopts)
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
                                                            (Prims.int_one +
                                                               i)), x)))
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
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___183_1471.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1475 -> failwith "impossible"
  
let (generalize_and_inst_within :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
          Prims.list))
  =
  fun env  ->
    fun tcs  ->
      fun datas  ->
        let binders =
          FStar_All.pipe_right tcs
            (FStar_List.map
               (fun uu____1566  ->
                  match uu____1566 with
                  | (se,uu____1572) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1573,uu____1574,tps,k,uu____1577,uu____1578)
                           ->
                           let uu____1587 =
                             let uu____1588 = FStar_Syntax_Syntax.mk_Total k
                                in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1588
                              in
                           FStar_Syntax_Syntax.null_binder uu____1587
                       | uu____1593 -> failwith "Impossible")))
           in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1622,uu____1623,t,uu____1625,uu____1626,uu____1627)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1634 -> failwith "Impossible"))
           in
        let t =
          let uu____1639 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1639
           in
        (let uu____1649 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses")
            in
         if uu____1649
         then
           let uu____1654 = FStar_TypeChecker_Normalize.term_to_string env t
              in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1654
         else ());
        (let uu____1659 = FStar_TypeChecker_Util.generalize_universes env t
            in
         match uu____1659 with
         | (uvs,t1) ->
             ((let uu____1679 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses")
                  in
               if uu____1679
               then
                 let uu____1684 =
                   let uu____1686 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                      in
                   FStar_All.pipe_right uu____1686 (FStar_String.concat ", ")
                    in
                 let uu____1703 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1684 uu____1703
               else ());
              (let uu____1708 = FStar_Syntax_Subst.open_univ_vars uvs t1  in
               match uu____1708 with
               | (uvs1,t2) ->
                   let uu____1723 = FStar_Syntax_Util.arrow_formals t2  in
                   (match uu____1723 with
                    | (args,uu____1747) ->
                        let uu____1768 =
                          FStar_Util.first_N (FStar_List.length binders) args
                           in
                        (match uu____1768 with
                         | (tc_types,data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1873  ->
                                    fun uu____1874  ->
                                      match (uu____1873, uu____1874) with
                                      | ((x,uu____1896),(se,uu____1898)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc,uu____1914,tps,uu____1916,mutuals,datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let uu____1928 =
                                                 let uu____1933 =
                                                   let uu____1934 =
                                                     FStar_Syntax_Subst.compress
                                                       ty
                                                      in
                                                   uu____1934.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____1933 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1,c) ->
                                                     let uu____1963 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1
                                                        in
                                                     (match uu____1963 with
                                                      | (tps1,rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____2041 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  FStar_Pervasives_Native.None
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                             in
                                                          (tps1, t3))
                                                 | uu____2060 -> ([], ty)  in
                                               (match uu____1928 with
                                                | (tps1,t3) ->
                                                    let uu___260_2069 = se
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
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___260_2069.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____2074 ->
                                               failwith "Impossible"))
                                 tc_types tcs
                                in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____2081 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun _2085  ->
                                             FStar_Syntax_Syntax.U_name _2085))
                                      in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_2105  ->
                                             match uu___0_2105 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc,uu____2111,uu____2112,uu____2113,uu____2114,uu____2115);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____2116;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____2117;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____2118;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____2119;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____2120;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2135 ->
                                                 failwith "Impossible"))
                                      in
                                   FStar_List.map2
                                     (fun uu____2159  ->
                                        fun d  ->
                                          match uu____2159 with
                                          | (t3,uu____2168) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l,uu____2174,uu____2175,tc,ntps,mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2186 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2186
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1)
                                                      in
                                                   let uu___297_2187 = d  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___297_2187.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___297_2187.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___297_2187.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___297_2187.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___297_2187.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu____2191 ->
                                                   failwith "Impossible"))
                                     data_types datas
                                in
                             (tcs1, datas1))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____2210 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2210
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2232 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2232
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____2249 =
      let uu____2250 = FStar_Syntax_Subst.compress t  in
      uu____2250.FStar_Syntax_Syntax.n  in
    match uu____2249 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2269 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2275 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____2312 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2361  ->
               match uu____2361 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2405 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2405  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2312
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2610 =
             let uu____2612 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____2612
              in
           debug_log env uu____2610);
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
           (let uu____2617 =
              let uu____2619 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____2619
               in
            debug_log env uu____2617);
           (let uu____2624 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2624) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2637 =
                  let uu____2638 = FStar_Syntax_Subst.compress btype1  in
                  uu____2638.FStar_Syntax_Syntax.n  in
                match uu____2637 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2668 = try_get_fv t  in
                    (match uu____2668 with
                     | (fv,us) ->
                         let uu____2676 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2676
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2692  ->
                                 match uu____2692 with
                                 | (t1,uu____2701) ->
                                     let uu____2706 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2706) args)
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
                          let uu____2741 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2741
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2745 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2745
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
                            (fun uu____2772  ->
                               match uu____2772 with
                               | (b,uu____2781) ->
                                   let uu____2786 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2786) sbs)
                           &&
                           ((let uu____2792 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2792 with
                             | (uu____2798,return_type) ->
                                 let uu____2800 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2800)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2801 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2805 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2810) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2818) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2825,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2884  ->
                          match uu____2884 with
                          | (p,uu____2897,t) ->
                              let bs =
                                let uu____2916 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2916
                                 in
                              let uu____2925 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2925 with
                               | (bs1,t1) ->
                                   let uu____2933 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2933)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2935,uu____2936)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____2979 ->
                    ((let uu____2981 =
                        let uu____2983 =
                          let uu____2985 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____2987 =
                            let uu____2989 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____2989  in
                          Prims.op_Hat uu____2985 uu____2987  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____2983
                         in
                      debug_log env uu____2981);
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
              (let uu____3002 =
                 let uu____3004 =
                   let uu____3006 =
                     let uu____3008 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____3008  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____3006  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____3004
                  in
               debug_log env uu____3002);
              (let uu____3012 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3012 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3031 =
                       let uu____3033 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3033
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____3031
                      then
                        ((let uu____3037 =
                            let uu____3039 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____3039
                             in
                          debug_log env uu____3037);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____3050 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3050
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____3061 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3061  in
                         (let uu____3067 =
                            let uu____3069 =
                              let uu____3071 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____3071
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____3069
                             in
                          debug_log env uu____3067);
                         (let uu____3076 =
                            let uu____3077 = FStar_ST.op_Bang unfolded  in
                            let uu____3103 =
                              let uu____3110 =
                                let uu____3115 =
                                  let uu____3116 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3116  in
                                (ilid, uu____3115)  in
                              [uu____3110]  in
                            FStar_List.append uu____3077 uu____3103  in
                          FStar_ST.op_Colon_Equals unfolded uu____3076);
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
                  (let uu____3215 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3215 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3238 ->
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
                         (let uu____3242 =
                            let uu____3244 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____3244
                             in
                          debug_log env uu____3242);
                         (let uu____3247 =
                            let uu____3248 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3248.FStar_Syntax_Syntax.n  in
                          match uu____3247 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3276 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3276 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3340 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3340 dbs1
                                       in
                                    let c1 =
                                      let uu____3344 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3344 c
                                       in
                                    let uu____3347 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3347 with
                                     | (args1,uu____3382) ->
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
                                           let uu____3474 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3474 c1
                                            in
                                         ((let uu____3484 =
                                             let uu____3486 =
                                               let uu____3488 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3491 =
                                                 let uu____3493 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____3493
                                                  in
                                               Prims.op_Hat uu____3488
                                                 uu____3491
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3486
                                              in
                                           debug_log env uu____3484);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3507 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3510 =
                                  let uu____3511 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3511.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3510
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
                   (let uu____3550 = try_get_fv t1  in
                    match uu____3550 with
                    | (fv,uu____3557) ->
                        let uu____3558 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3558
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3590 =
                      let uu____3592 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3592
                       in
                    debug_log env uu____3590);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3597 =
                      FStar_List.fold_left
                        (fun uu____3618  ->
                           fun b  ->
                             match uu____3618 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3649 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3653 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3649, uu____3653))) (true, env)
                        sbs1
                       in
                    match uu____3597 with | (b,uu____3671) -> b))
              | uu____3674 ->
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
              let uu____3710 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3710 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3733 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3736 =
                      let uu____3738 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____3738
                       in
                    debug_log env uu____3736);
                   (let uu____3741 =
                      let uu____3742 = FStar_Syntax_Subst.compress dt  in
                      uu____3742.FStar_Syntax_Syntax.n  in
                    match uu____3741 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3746 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3751) ->
                        let dbs1 =
                          let uu____3781 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3781  in
                        let dbs2 =
                          let uu____3831 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3831 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3836 =
                            let uu____3838 =
                              let uu____3840 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____3840 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3838
                             in
                          debug_log env uu____3836);
                         (let uu____3850 =
                            FStar_List.fold_left
                              (fun uu____3871  ->
                                 fun b  ->
                                   match uu____3871 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3902 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3906 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3902, uu____3906)))
                              (true, env) dbs3
                             in
                          match uu____3850 with | (b,uu____3924) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3927,uu____3928) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3964 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____3987 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4003,uu____4004,uu____4005) -> (lid, us, bs)
        | uu____4014 -> failwith "Impossible!"  in
      match uu____3987 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4026 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4026 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4050 =
                 let uu____4053 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4053  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4067 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4067
                      unfolded_inductives env2) uu____4050)
  
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
        (uu____4102,uu____4103,t,uu____4105,uu____4106,uu____4107) -> t
    | uu____4114 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4131 =
         let uu____4133 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4133 haseq_suffix  in
       uu____4131 = Prims.int_zero)
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4143 =
      let uu____4146 =
        let uu____4149 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4149]  in
      FStar_List.append lid.FStar_Ident.ns uu____4146  in
    FStar_Ident.lid_of_ids uu____4143
  
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
          let uu____4195 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4209,bs,t,uu____4212,uu____4213) -> (lid, bs, t)
            | uu____4222 -> failwith "Impossible!"  in
          match uu____4195 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4245 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4245 t  in
              let uu____4254 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4254 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4272 =
                       let uu____4273 = FStar_Syntax_Subst.compress t2  in
                       uu____4273.FStar_Syntax_Syntax.n  in
                     match uu____4272 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4277) -> ibs
                     | uu____4298 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4307 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4308 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4307 uu____4308
                      in
                   let ind1 =
                     let uu____4314 =
                       let uu____4319 =
                         FStar_List.map
                           (fun uu____4336  ->
                              match uu____4336 with
                              | (bv,aq) ->
                                  let uu____4355 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4355, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4319  in
                     uu____4314 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4361 =
                       let uu____4366 =
                         FStar_List.map
                           (fun uu____4383  ->
                              match uu____4383 with
                              | (bv,aq) ->
                                  let uu____4402 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4402, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4366  in
                     uu____4361 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4408 =
                       let uu____4413 =
                         let uu____4414 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4414]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4413
                        in
                     uu____4408 FStar_Pervasives_Native.None
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
                     let uu___631_4518 = fml  in
                     let uu____4519 =
                       let uu____4520 =
                         let uu____4527 =
                           let uu____4528 =
                             let uu____4549 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____4554 =
                               let uu____4567 =
                                 let uu____4578 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____4578]  in
                               [uu____4567]  in
                             (uu____4549, uu____4554)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4528  in
                         (fml, uu____4527)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4520  in
                     {
                       FStar_Syntax_Syntax.n = uu____4519;
                       FStar_Syntax_Syntax.pos =
                         (uu___631_4518.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___631_4518.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4647 =
                              let uu____4652 =
                                let uu____4653 =
                                  let uu____4662 =
                                    let uu____4663 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4663 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4662  in
                                [uu____4653]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4652
                               in
                            uu____4647 FStar_Pervasives_Native.None
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
          let uu____4807 =
            let uu____4808 = FStar_Syntax_Subst.compress dt1  in
            uu____4808.FStar_Syntax_Syntax.n  in
          match uu____4807 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4812) ->
              let dbs1 =
                let uu____4842 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4842  in
              let dbs2 =
                let uu____4892 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4892 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4907 =
                           let uu____4912 =
                             let uu____4913 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4913]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4912
                            in
                         uu____4907 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4944 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4944 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4952 =
                       let uu____4957 =
                         let uu____4958 =
                           let uu____4967 =
                             let uu____4968 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4968
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4967  in
                         [uu____4958]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4957
                        in
                     uu____4952 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5015 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5106,uu____5107,uu____5108,uu____5109,uu____5110)
                  -> lid
              | uu____5119 -> failwith "Impossible!"  in
            let uu____5121 = acc  in
            match uu____5121 with
            | (uu____5158,en,uu____5160,uu____5161) ->
                let uu____5182 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5182 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5219 = acc  in
                     (match uu____5219 with
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
                                     (uu____5294,uu____5295,uu____5296,t_lid,uu____5298,uu____5299)
                                     -> t_lid = lid
                                 | uu____5306 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5321 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5321)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5324 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5327 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5324, uu____5327)))
  
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
          let uu____5385 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5395,us,uu____5397,t,uu____5399,uu____5400) -> 
                (us, t)
            | uu____5409 -> failwith "Impossible!"  in
          match uu____5385 with
          | (us,t) ->
              let uu____5419 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5419 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5445 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5445 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5523 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5523 with
                           | (uu____5538,t1) ->
                               let uu____5560 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5560
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5565 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5565 with
                          | (phi1,uu____5573) ->
                              ((let uu____5575 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5575
                                then
                                  let uu____5578 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5578
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5596  ->
                                         match uu____5596 with
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
                                                    = [];
                                                  FStar_Syntax_Syntax.sigopts
                                                    =
                                                    FStar_Pervasives_Native.None
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
                let uu____5668 =
                  let uu____5669 = FStar_Syntax_Subst.compress t  in
                  uu____5669.FStar_Syntax_Syntax.n  in
                match uu____5668 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5677) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5714 = is_mutual t'  in
                    if uu____5714
                    then true
                    else
                      (let uu____5721 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5721)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5741) -> is_mutual t'
                | uu____5746 -> false
              
              and exists_mutual uu___1_5748 =
                match uu___1_5748 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5769 =
                let uu____5770 = FStar_Syntax_Subst.compress dt1  in
                uu____5770.FStar_Syntax_Syntax.n  in
              match uu____5769 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5776) ->
                  let dbs1 =
                    let uu____5806 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5806  in
                  let dbs2 =
                    let uu____5856 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5856 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5876 =
                               let uu____5881 =
                                 let uu____5882 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5882]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5881
                                in
                             uu____5876 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5912 = is_mutual sort  in
                             if uu____5912
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
                           let uu____5925 =
                             let uu____5930 =
                               let uu____5931 =
                                 let uu____5940 =
                                   let uu____5941 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5941 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5940  in
                               [uu____5931]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5930
                              in
                           uu____5925 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____5988 -> acc
  
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
              let uu____6038 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6060,bs,t,uu____6063,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6075 -> failwith "Impossible!"  in
              match uu____6038 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6099 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6099 t  in
                  let uu____6108 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6108 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6118 =
                           let uu____6119 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6119.FStar_Syntax_Syntax.n  in
                         match uu____6118 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6123) ->
                             ibs
                         | uu____6144 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6153 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6154 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6153
                           uu____6154
                          in
                       let ind1 =
                         let uu____6160 =
                           let uu____6165 =
                             FStar_List.map
                               (fun uu____6182  ->
                                  match uu____6182 with
                                  | (bv,aq) ->
                                      let uu____6201 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6201, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6165  in
                         uu____6160 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6207 =
                           let uu____6212 =
                             FStar_List.map
                               (fun uu____6229  ->
                                  match uu____6229 with
                                  | (bv,aq) ->
                                      let uu____6248 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6248, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6212  in
                         uu____6207 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6254 =
                           let uu____6259 =
                             let uu____6260 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6260]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6259
                            in
                         uu____6254 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6297,uu____6298,uu____6299,t_lid,uu____6301,uu____6302)
                                  -> t_lid = lid
                              | uu____6309 -> failwith "Impossible")
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
                         let uu___868_6321 = fml  in
                         let uu____6322 =
                           let uu____6323 =
                             let uu____6330 =
                               let uu____6331 =
                                 let uu____6352 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____6357 =
                                   let uu____6370 =
                                     let uu____6381 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____6381]  in
                                   [uu____6370]  in
                                 (uu____6352, uu____6357)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6331
                                in
                             (fml, uu____6330)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6323  in
                         {
                           FStar_Syntax_Syntax.n = uu____6322;
                           FStar_Syntax_Syntax.pos =
                             (uu___868_6321.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___868_6321.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6450 =
                                  let uu____6455 =
                                    let uu____6456 =
                                      let uu____6465 =
                                        let uu____6466 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6466
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6465
                                       in
                                    [uu____6456]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6455
                                   in
                                uu____6450 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6519 =
                                  let uu____6524 =
                                    let uu____6525 =
                                      let uu____6534 =
                                        let uu____6535 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6535
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6534
                                       in
                                    [uu____6525]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6524
                                   in
                                uu____6519 FStar_Pervasives_Native.None
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
                     (lid,uu____6627,uu____6628,uu____6629,uu____6630,uu____6631)
                     -> lid
                 | uu____6640 -> failwith "Impossible!") tcs
             in
          let uu____6642 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6654,uu____6655,uu____6656,uu____6657) ->
                (lid, us)
            | uu____6666 -> failwith "Impossible!"  in
          match uu____6642 with
          | (lid,us) ->
              let uu____6676 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6676 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6703 =
                       let uu____6704 =
                         let uu____6711 = get_haseq_axiom_lid lid  in
                         (uu____6711, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6704  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6703;
                       FStar_Syntax_Syntax.sigrng = FStar_Range.dummyRange;
                       FStar_Syntax_Syntax.sigquals = [];
                       FStar_Syntax_Syntax.sigmeta =
                         FStar_Syntax_Syntax.default_sigmeta;
                       FStar_Syntax_Syntax.sigattrs = [];
                       FStar_Syntax_Syntax.sigopts =
                         FStar_Pervasives_Native.None
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
          let uu____6765 =
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
                        FStar_Syntax_Syntax.sigattrs = uu____6797;
                        FStar_Syntax_Syntax.sigopts = uu____6798;_} -> true
                    | uu____6822 -> false))
             in
          match uu____6765 with
          | (tys,datas) ->
              ((let uu____6845 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6857  ->
                          match uu___3_6857 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6859;
                              FStar_Syntax_Syntax.sigrng = uu____6860;
                              FStar_Syntax_Syntax.sigquals = uu____6861;
                              FStar_Syntax_Syntax.sigmeta = uu____6862;
                              FStar_Syntax_Syntax.sigattrs = uu____6863;
                              FStar_Syntax_Syntax.sigopts = uu____6864;_} ->
                              false
                          | uu____6887 -> true))
                   in
                if uu____6845
                then
                  let uu____6890 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6890
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6905 =
                       let uu____6906 = FStar_List.hd tys  in
                       uu____6906.FStar_Syntax_Syntax.sigel  in
                     match uu____6905 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6909,uvs,uu____6911,uu____6912,uu____6913,uu____6914)
                         -> uvs
                     | uu____6923 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6928 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____6967  ->
                         match uu____6967 with
                         | (env1,all_tcs,g) ->
                             let uu____7007 = tc_tycon env1 tc  in
                             (match uu____7007 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____7034 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____7034
                                    then
                                      let uu____7037 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____7037
                                    else ());
                                   (let uu____7042 =
                                      let uu____7043 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____7043
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____7042))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard)
                   in
                match uu____6928 with
                | (env1,tcs,g) ->
                    let uu____7089 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____7111  ->
                             match uu____7111 with
                             | (datas1,g1) ->
                                 let uu____7130 =
                                   let uu____7135 = tc_data env1 tcs  in
                                   uu____7135 se  in
                                 (match uu____7130 with
                                  | (data,g') ->
                                      let uu____7152 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____7152))) datas
                        ([], g)
                       in
                    (match uu____7089 with
                     | (datas1,g1) ->
                         let uu____7173 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs
                              in
                           let g2 =
                             let uu___979_7190 = g1  in
                             {
                               FStar_TypeChecker_Env.guard_f =
                                 (uu___979_7190.FStar_TypeChecker_Env.guard_f);
                               FStar_TypeChecker_Env.deferred =
                                 (uu___979_7190.FStar_TypeChecker_Env.deferred);
                               FStar_TypeChecker_Env.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Env.univ_ineqs));
                               FStar_TypeChecker_Env.implicits =
                                 (uu___979_7190.FStar_TypeChecker_Env.implicits)
                             }  in
                           (let uu____7200 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses")
                               in
                            if uu____7200
                            then
                              let uu____7205 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2
                                 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____7205
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs1) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____7224 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs
                                 in
                              (uu____7224, datas1))
                            in
                         (match uu____7173 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____7256 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                let uu____7257 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses
                                   in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____7256;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____7257;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                }  in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs2,binders,typ,uu____7283,uu____7284)
                                           ->
                                           let fail1 expected inferred =
                                             let uu____7304 =
                                               let uu____7310 =
                                                 let uu____7312 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected
                                                    in
                                                 let uu____7314 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred
                                                    in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____7312 uu____7314
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____7310)
                                                in
                                             FStar_Errors.raise_error
                                               uu____7304
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
                                                (expected_typ1,uu____7334) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____7365 ->
                                                        let uu____7366 =
                                                          let uu____7373 =
                                                            let uu____7374 =
                                                              let uu____7389
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ
                                                                 in
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
                                                  (FStar_List.length univs2)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ1))
                                                then
                                                  let uu____7411 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ
                                                     in
                                                  (match uu____7411 with
                                                   | (uu____7416,inferred) ->
                                                       let uu____7418 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1
                                                          in
                                                       (match uu____7418 with
                                                        | (uu____7423,expected)
                                                            ->
                                                            let uu____7425 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected
                                                               in
                                                            if uu____7425
                                                            then ()
                                                            else
                                                              fail1
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail1 expected_typ1
                                                    inferred_typ)
                                       | uu____7432 -> ()));
                               (sig_bndle, tcs1, datas2))))))
  
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
                      Prims.bool -> FStar_Syntax_Syntax.sigelt Prims.list)
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
                      fun erasable1  ->
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
                            let uu____7550 =
                              let uu____7557 =
                                let uu____7558 =
                                  let uu____7565 =
                                    let uu____7568 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7568
                                     in
                                  (uu____7565, inst_univs)  in
                                FStar_Syntax_Syntax.Tm_uinst uu____7558  in
                              FStar_Syntax_Syntax.mk uu____7557  in
                            uu____7550 FStar_Pervasives_Native.None p  in
                          let args =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7602  ->
                                    match uu____7602 with
                                    | (x,imp) ->
                                        let uu____7621 =
                                          FStar_Syntax_Syntax.bv_to_name x
                                           in
                                        (uu____7621, imp)))
                             in
                          FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                            FStar_Pervasives_Native.None p
                           in
                        let unrefined_arg_binder =
                          let uu____7625 = projectee arg_typ  in
                          FStar_Syntax_Syntax.mk_binder uu____7625  in
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
                                 let uu____7648 =
                                   FStar_Ident.set_lid_range disc_name p  in
                                 FStar_Syntax_Syntax.fvar uu____7648
                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                      Prims.int_one)
                                   FStar_Pervasives_Native.None
                                  in
                               let uu____7650 =
                                 let uu____7653 =
                                   let uu____7656 =
                                     let uu____7661 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs
                                        in
                                     let uu____7662 =
                                       let uu____7663 =
                                         let uu____7672 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7672
                                          in
                                       [uu____7663]  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7661
                                       uu____7662
                                      in
                                   uu____7656 FStar_Pervasives_Native.None p
                                    in
                                 FStar_Syntax_Util.b2t uu____7653  in
                               FStar_Syntax_Util.refine x uu____7650  in
                             let uu____7697 =
                               let uu___1053_7698 = projectee arg_typ  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1053_7698.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1053_7698.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = sort
                               }  in
                             FStar_Syntax_Syntax.mk_binder uu____7697)
                           in
                        let ntps = FStar_List.length tps  in
                        let all_params =
                          let uu____7715 =
                            FStar_List.map
                              (fun uu____7739  ->
                                 match uu____7739 with
                                 | (x,uu____7753) ->
                                     (x,
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.imp_tag))) tps
                             in
                          FStar_List.append uu____7715 fields  in
                        let imp_binders =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7812  ->
                                  match uu____7812 with
                                  | (x,uu____7826) ->
                                      (x,
                                        (FStar_Pervasives_Native.Some
                                           FStar_Syntax_Syntax.imp_tag))))
                           in
                        let early_prims_inductive =
                          (let uu____7837 =
                             FStar_TypeChecker_Env.current_module env  in
                           FStar_Ident.lid_equals
                             FStar_Parser_Const.prims_lid uu____7837)
                            &&
                            (FStar_List.existsb
                               (fun s  ->
                                  s =
                                    (tc.FStar_Ident.ident).FStar_Ident.idText)
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
                                 (let uu____7858 =
                                    let uu____7860 =
                                      FStar_TypeChecker_Env.current_module
                                        env
                                       in
                                    uu____7860.FStar_Ident.str  in
                                  FStar_Options.dont_gen_projectors
                                    uu____7858)
                                in
                             let quals =
                               let uu____7864 =
                                 FStar_List.filter
                                   (fun uu___4_7868  ->
                                      match uu___4_7868 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Inline_for_extraction
                                           -> true
                                      | FStar_Syntax_Syntax.NoExtract  ->
                                          true
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7873 -> false) iquals
                                  in
                               FStar_List.append
                                 ((FStar_Syntax_Syntax.Discriminator lid) ::
                                 (if only_decl
                                  then
                                    [FStar_Syntax_Syntax.Logic;
                                    FStar_Syntax_Syntax.Assumption]
                                  else [])) uu____7864
                                in
                             let binders =
                               FStar_List.append imp_binders
                                 [unrefined_arg_binder]
                                in
                             let t =
                               let bool_typ =
                                 if erasable1
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal
                                     FStar_Syntax_Util.t_bool
                                 else
                                   FStar_Syntax_Syntax.mk_Total
                                     FStar_Syntax_Util.t_bool
                                  in
                               let uu____7918 =
                                 FStar_Syntax_Util.arrow binders bool_typ  in
                               FStar_All.pipe_left
                                 (FStar_Syntax_Subst.close_univ_vars uvs)
                                 uu____7918
                                in
                             let decl =
                               let uu____7922 =
                                 FStar_Ident.range_of_lid discriminator_name
                                  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (discriminator_name, uvs, t));
                                 FStar_Syntax_Syntax.sigrng = uu____7922;
                                 FStar_Syntax_Syntax.sigquals = quals;
                                 FStar_Syntax_Syntax.sigmeta =
                                   FStar_Syntax_Syntax.default_sigmeta;
                                 FStar_Syntax_Syntax.sigattrs = [];
                                 FStar_Syntax_Syntax.sigopts =
                                   FStar_Pervasives_Native.None
                               }  in
                             (let uu____7924 =
                                FStar_TypeChecker_Env.debug env
                                  (FStar_Options.Other "LogTypes")
                                 in
                              if uu____7924
                              then
                                let uu____7928 =
                                  FStar_Syntax_Print.sigelt_to_string decl
                                   in
                                FStar_Util.print1
                                  "Declaration of a discriminator %s\n"
                                  uu____7928
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
                                               fun uu____7989  ->
                                                 match uu____7989 with
                                                 | (x,imp) ->
                                                     let b =
                                                       FStar_Syntax_Syntax.is_implicit
                                                         imp
                                                        in
                                                     if b && (j < ntps)
                                                     then
                                                       let uu____8014 =
                                                         let uu____8017 =
                                                           let uu____8018 =
                                                             let uu____8025 =
                                                               FStar_Syntax_Syntax.gen_bv
                                                                 (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                 FStar_Pervasives_Native.None
                                                                 FStar_Syntax_Syntax.tun
                                                                in
                                                             (uu____8025,
                                                               FStar_Syntax_Syntax.tun)
                                                              in
                                                           FStar_Syntax_Syntax.Pat_dot_term
                                                             uu____8018
                                                            in
                                                         pos uu____8017  in
                                                       (uu____8014, b)
                                                     else
                                                       (let uu____8033 =
                                                          let uu____8036 =
                                                            let uu____8037 =
                                                              FStar_Syntax_Syntax.gen_bv
                                                                (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                FStar_Pervasives_Native.None
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            FStar_Syntax_Syntax.Pat_wild
                                                              uu____8037
                                                             in
                                                          pos uu____8036  in
                                                        (uu____8033, b))))
                                        in
                                     let pat_true =
                                       let uu____8056 =
                                         let uu____8059 =
                                           let uu____8060 =
                                             let uu____8074 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 lid
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    fvq)
                                                in
                                             (uu____8074, arg_pats)  in
                                           FStar_Syntax_Syntax.Pat_cons
                                             uu____8060
                                            in
                                         pos uu____8059  in
                                       (uu____8056,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_true_bool)
                                        in
                                     let pat_false =
                                       let uu____8109 =
                                         let uu____8112 =
                                           let uu____8113 =
                                             FStar_Syntax_Syntax.new_bv
                                               FStar_Pervasives_Native.None
                                               FStar_Syntax_Syntax.tun
                                              in
                                           FStar_Syntax_Syntax.Pat_wild
                                             uu____8113
                                            in
                                         pos uu____8112  in
                                       (uu____8109,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_false_bool)
                                        in
                                     let arg_exp =
                                       FStar_Syntax_Syntax.bv_to_name
                                         (FStar_Pervasives_Native.fst
                                            unrefined_arg_binder)
                                        in
                                     let uu____8127 =
                                       let uu____8134 =
                                         let uu____8135 =
                                           let uu____8158 =
                                             let uu____8175 =
                                               FStar_Syntax_Util.branch
                                                 pat_true
                                                in
                                             let uu____8190 =
                                               let uu____8207 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false
                                                  in
                                               [uu____8207]  in
                                             uu____8175 :: uu____8190  in
                                           (arg_exp, uu____8158)  in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____8135
                                          in
                                       FStar_Syntax_Syntax.mk uu____8134  in
                                     uu____8127 FStar_Pervasives_Native.None
                                       p)
                                   in
                                let dd =
                                  let uu____8283 =
                                    FStar_All.pipe_right quals
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Abstract)
                                     in
                                  if uu____8283
                                  then
                                    FStar_Syntax_Syntax.Delta_abstract
                                      (FStar_Syntax_Syntax.Delta_equational_at_level
                                         Prims.int_one)
                                  else
                                    FStar_Syntax_Syntax.Delta_equational_at_level
                                      Prims.int_one
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
                                  let uu____8305 =
                                    let uu____8310 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        discriminator_name dd
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Util.Inr uu____8310  in
                                  let uu____8311 =
                                    FStar_Syntax_Subst.close_univ_vars uvs
                                      imp
                                     in
                                  FStar_Syntax_Util.mk_letbinding uu____8305
                                    uvs lbtyp
                                    FStar_Parser_Const.effect_Tot_lid
                                    uu____8311 [] FStar_Range.dummyRange
                                   in
                                let impl =
                                  let uu____8317 =
                                    let uu____8318 =
                                      let uu____8325 =
                                        let uu____8328 =
                                          let uu____8329 =
                                            FStar_All.pipe_right
                                              lb.FStar_Syntax_Syntax.lbname
                                              FStar_Util.right
                                             in
                                          FStar_All.pipe_right uu____8329
                                            (fun fv  ->
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                           in
                                        [uu____8328]  in
                                      ((false, [lb]), uu____8325)  in
                                    FStar_Syntax_Syntax.Sig_let uu____8318
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____8317;
                                    FStar_Syntax_Syntax.sigrng = p;
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = [];
                                    FStar_Syntax_Syntax.sigopts =
                                      FStar_Pervasives_Native.None
                                  }  in
                                (let uu____8343 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "LogTypes")
                                    in
                                 if uu____8343
                                 then
                                   let uu____8347 =
                                     FStar_Syntax_Print.sigelt_to_string impl
                                      in
                                   FStar_Util.print1
                                     "Implementation of a discriminator %s\n"
                                     uu____8347
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
                                  fun uu____8420  ->
                                    match uu____8420 with
                                    | (a,uu____8429) ->
                                        let uu____8434 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid a i
                                           in
                                        (match uu____8434 with
                                         | (field_name,uu____8440) ->
                                             let field_proj_tm =
                                               let uu____8442 =
                                                 let uu____8443 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     field_name
                                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                                        Prims.int_one)
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____8443
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_uinst
                                                 uu____8442 inst_univs
                                                in
                                             let proj =
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 field_proj_tm [arg]
                                                 FStar_Pervasives_Native.None
                                                 p
                                                in
                                             FStar_Syntax_Syntax.NT (a, proj))))
                           in
                        let projectors_ses =
                          let uu____8469 =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i  ->
                                    fun uu____8511  ->
                                      match uu____8511 with
                                      | (x,uu____8522) ->
                                          let p1 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          let uu____8528 =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid x i
                                             in
                                          (match uu____8528 with
                                           | (field_name,uu____8536) ->
                                               let t =
                                                 let result_comp =
                                                   let t =
                                                     FStar_Syntax_Subst.subst
                                                       subst1
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   if erasable1
                                                   then
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                   else
                                                     FStar_Syntax_Syntax.mk_Total
                                                       t
                                                    in
                                                 let uu____8549 =
                                                   FStar_Syntax_Util.arrow
                                                     binders result_comp
                                                    in
                                                 FStar_All.pipe_left
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      uvs) uu____8549
                                                  in
                                               let only_decl =
                                                 early_prims_inductive ||
                                                   (let uu____8555 =
                                                      let uu____8557 =
                                                        FStar_TypeChecker_Env.current_module
                                                          env
                                                         in
                                                      uu____8557.FStar_Ident.str
                                                       in
                                                    FStar_Options.dont_gen_projectors
                                                      uu____8555)
                                                  in
                                               let no_decl = false  in
                                               let quals q =
                                                 if only_decl
                                                 then
                                                   let uu____8576 =
                                                     FStar_List.filter
                                                       (fun uu___5_8580  ->
                                                          match uu___5_8580
                                                          with
                                                          | FStar_Syntax_Syntax.Abstract
                                                               -> false
                                                          | uu____8583 ->
                                                              true) q
                                                      in
                                                   FStar_Syntax_Syntax.Assumption
                                                     :: uu____8576
                                                 else q  in
                                               let quals1 =
                                                 let iquals1 =
                                                   FStar_All.pipe_right
                                                     iquals
                                                     (FStar_List.filter
                                                        (fun uu___6_8598  ->
                                                           match uu___6_8598
                                                           with
                                                           | FStar_Syntax_Syntax.Inline_for_extraction
                                                                -> true
                                                           | FStar_Syntax_Syntax.NoExtract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Abstract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Private
                                                                -> true
                                                           | uu____8604 ->
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
                                                 let uu____8615 =
                                                   FStar_Ident.range_of_lid
                                                     field_name
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                                        (field_name, uvs, t));
                                                   FStar_Syntax_Syntax.sigrng
                                                     = uu____8615;
                                                   FStar_Syntax_Syntax.sigquals
                                                     = quals1;
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     FStar_Syntax_Syntax.default_sigmeta;
                                                   FStar_Syntax_Syntax.sigattrs
                                                     = attrs;
                                                   FStar_Syntax_Syntax.sigopts
                                                     =
                                                     FStar_Pervasives_Native.None
                                                 }  in
                                               ((let uu____8617 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes")
                                                    in
                                                 if uu____8617
                                                 then
                                                   let uu____8621 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       decl
                                                      in
                                                   FStar_Util.print1
                                                     "Declaration of a projector %s\n"
                                                     uu____8621
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
                                                             fun uu____8675 
                                                               ->
                                                               match uu____8675
                                                               with
                                                               | (x1,imp) ->
                                                                   let b =
                                                                    FStar_Syntax_Syntax.is_implicit
                                                                    imp  in
                                                                   if
                                                                    (i + ntps)
                                                                    = j
                                                                   then
                                                                    let uu____8701
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                    (uu____8701,
                                                                    b)
                                                                   else
                                                                    if
                                                                    b &&
                                                                    (j < ntps)
                                                                    then
                                                                    (let uu____8717
                                                                    =
                                                                    let uu____8720
                                                                    =
                                                                    let uu____8721
                                                                    =
                                                                    let uu____8728
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8728,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8721
                                                                     in
                                                                    pos
                                                                    uu____8720
                                                                     in
                                                                    (uu____8717,
                                                                    b))
                                                                    else
                                                                    (let uu____8736
                                                                    =
                                                                    let uu____8739
                                                                    =
                                                                    let uu____8740
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8740
                                                                     in
                                                                    pos
                                                                    uu____8739
                                                                     in
                                                                    (uu____8736,
                                                                    b))))
                                                      in
                                                   let pat =
                                                     let uu____8759 =
                                                       let uu____8762 =
                                                         let uu____8763 =
                                                           let uu____8777 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               lid
                                                               FStar_Syntax_Syntax.delta_constant
                                                               (FStar_Pervasives_Native.Some
                                                                  fvq)
                                                              in
                                                           (uu____8777,
                                                             arg_pats)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_cons
                                                           uu____8763
                                                          in
                                                       pos uu____8762  in
                                                     let uu____8787 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         projection
                                                        in
                                                     (uu____8759,
                                                       FStar_Pervasives_Native.None,
                                                       uu____8787)
                                                      in
                                                   let body =
                                                     let uu____8803 =
                                                       let uu____8810 =
                                                         let uu____8811 =
                                                           let uu____8834 =
                                                             let uu____8851 =
                                                               FStar_Syntax_Util.branch
                                                                 pat
                                                                in
                                                             [uu____8851]  in
                                                           (arg_exp,
                                                             uu____8834)
                                                            in
                                                         FStar_Syntax_Syntax.Tm_match
                                                           uu____8811
                                                          in
                                                       FStar_Syntax_Syntax.mk
                                                         uu____8810
                                                        in
                                                     uu____8803
                                                       FStar_Pervasives_Native.None
                                                       p1
                                                      in
                                                   let imp =
                                                     FStar_Syntax_Util.abs
                                                       binders body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   let dd =
                                                     let uu____8916 =
                                                       FStar_All.pipe_right
                                                         quals1
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.Abstract)
                                                        in
                                                     if uu____8916
                                                     then
                                                       FStar_Syntax_Syntax.Delta_abstract
                                                         (FStar_Syntax_Syntax.Delta_equational_at_level
                                                            Prims.int_one)
                                                     else
                                                       FStar_Syntax_Syntax.Delta_equational_at_level
                                                         Prims.int_one
                                                      in
                                                   let lbtyp =
                                                     if no_decl
                                                     then t
                                                     else
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let lb =
                                                     let uu____8935 =
                                                       let uu____8940 =
                                                         FStar_Syntax_Syntax.lid_as_fv
                                                           field_name dd
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       FStar_Util.Inr
                                                         uu____8940
                                                        in
                                                     let uu____8941 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         uvs imp
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.lbname
                                                         = uu____8935;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = lbtyp;
                                                       FStar_Syntax_Syntax.lbeff
                                                         =
                                                         FStar_Parser_Const.effect_Tot_lid;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____8941;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = [];
                                                       FStar_Syntax_Syntax.lbpos
                                                         =
                                                         FStar_Range.dummyRange
                                                     }  in
                                                   let impl =
                                                     let uu____8947 =
                                                       let uu____8948 =
                                                         let uu____8955 =
                                                           let uu____8958 =
                                                             let uu____8959 =
                                                               FStar_All.pipe_right
                                                                 lb.FStar_Syntax_Syntax.lbname
                                                                 FStar_Util.right
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____8959
                                                               (fun fv  ->
                                                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                              in
                                                           [uu____8958]  in
                                                         ((false, [lb]),
                                                           uu____8955)
                                                          in
                                                       FStar_Syntax_Syntax.Sig_let
                                                         uu____8948
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         = uu____8947;
                                                       FStar_Syntax_Syntax.sigrng
                                                         = p1;
                                                       FStar_Syntax_Syntax.sigquals
                                                         = quals1;
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         FStar_Syntax_Syntax.default_sigmeta;
                                                       FStar_Syntax_Syntax.sigattrs
                                                         = attrs;
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         FStar_Pervasives_Native.None
                                                     }  in
                                                   (let uu____8973 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        (FStar_Options.Other
                                                           "LogTypes")
                                                       in
                                                    if uu____8973
                                                    then
                                                      let uu____8977 =
                                                        FStar_Syntax_Print.sigelt_to_string
                                                          impl
                                                         in
                                                      FStar_Util.print1
                                                        "Implementation of a projector %s\n"
                                                        uu____8977
                                                    else ());
                                                   if no_decl
                                                   then [impl]
                                                   else [decl; impl])))))
                             in
                          FStar_All.pipe_right uu____8469 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____9031) when
              let uu____9038 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____9038 ->
              let uu____9040 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9040 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____9062 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____9062 with
                    | (formals,uu____9080) ->
                        let uu____9101 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____9136 =
                                   let uu____9138 =
                                     let uu____9139 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____9139  in
                                   FStar_Ident.lid_equals typ_lid uu____9138
                                    in
                                 if uu____9136
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9161,uvs',tps,typ0,uu____9165,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              Prims.int_one))
                                   | uu____9185 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9234 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9234
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____9101 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9272 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9272 with
                              | (indices,uu____9290) ->
                                  let refine_domain =
                                    let uu____9313 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___7_9320  ->
                                              match uu___7_9320 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9322 -> true
                                              | uu____9332 -> false))
                                       in
                                    if uu____9313
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___8_9347 =
                                      match uu___8_9347 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9350,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9362 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9363 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9363 with
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
                                    let uu____9376 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9376 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9459  ->
                                               fun uu____9460  ->
                                                 match (uu____9459,
                                                         uu____9460)
                                                 with
                                                 | ((x,uu____9486),(x',uu____9488))
                                                     ->
                                                     let uu____9509 =
                                                       let uu____9516 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9516)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9509) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  let erasable1 =
                                    FStar_Syntax_Util.has_attribute
                                      se.FStar_Syntax_Syntax.sigattrs
                                      FStar_Parser_Const.erasable_attr
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    iquals1 fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields erasable1))))
          | uu____9523 -> []
  