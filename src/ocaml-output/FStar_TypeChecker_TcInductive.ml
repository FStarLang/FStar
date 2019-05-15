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
                                        FStar_TypeChecker_Env.Eager_unfolding
                                          false;
                                        FStar_TypeChecker_Env.NoFullNorm;
                                        FStar_TypeChecker_Env.Exclude
                                          FStar_TypeChecker_Env.Beta] env_tps
                                        k3
                                       in
                                    let uu____192 =
                                      FStar_Syntax_Util.arrow_formals k4  in
                                    let uu____207 =
                                      let uu____208 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard_params g
                                         in
                                      FStar_TypeChecker_Rel.discharge_guard
                                        env_tps uu____208
                                       in
                                    (uu____192, uu____207)
                                 in
                              (match uu____143 with
                               | ((indices,t),guard) ->
                                   let k3 =
                                     let uu____271 =
                                       FStar_Syntax_Syntax.mk_Total t  in
                                     FStar_Syntax_Util.arrow indices
                                       uu____271
                                      in
                                   let uu____274 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____274 with
                                    | (t_type,u) ->
                                        let valid_type =
                                          ((FStar_Syntax_Util.is_eqtype_no_unrefine
                                              t)
                                             &&
                                             (let uu____292 =
                                                FStar_All.pipe_right
                                                  s.FStar_Syntax_Syntax.sigquals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Unopteq)
                                                 in
                                              Prims.op_Negation uu____292))
                                            ||
                                            (FStar_TypeChecker_Rel.teq_nosmt_force
                                               env1 t t_type)
                                           in
                                        (if Prims.op_Negation valid_type
                                         then
                                           (let uu____299 =
                                              let uu____305 =
                                                let uu____307 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t
                                                   in
                                                let uu____309 =
                                                  FStar_Ident.string_of_lid
                                                    tc
                                                   in
                                                FStar_Util.format2
                                                  "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                  uu____307 uu____309
                                                 in
                                              (FStar_Errors.Error_InductiveAnnotNotAType,
                                                uu____305)
                                               in
                                            FStar_Errors.raise_error
                                              uu____299
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
                                            let uu____322 =
                                              let uu____331 =
                                                FStar_All.pipe_right tps3
                                                  (FStar_Syntax_Subst.subst_binders
                                                     usubst1)
                                                 in
                                              let uu____348 =
                                                let uu____357 =
                                                  let uu____370 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      (FStar_List.length tps3)
                                                      usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst_binders
                                                    uu____370
                                                   in
                                                FStar_All.pipe_right indices
                                                  uu____357
                                                 in
                                              FStar_List.append uu____331
                                                uu____348
                                               in
                                            let uu____393 =
                                              let uu____396 =
                                                let uu____397 =
                                                  let uu____402 =
                                                    FStar_Syntax_Subst.shift_subst
                                                      ((FStar_List.length
                                                          tps3)
                                                         +
                                                         (FStar_List.length
                                                            indices)) usubst1
                                                     in
                                                  FStar_Syntax_Subst.subst
                                                    uu____402
                                                   in
                                                FStar_All.pipe_right t
                                                  uu____397
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____396
                                               in
                                            FStar_Syntax_Util.arrow uu____322
                                              uu____393
                                             in
                                          let tps4 =
                                            FStar_Syntax_Subst.close_binders
                                              tps3
                                             in
                                          let k4 =
                                            FStar_Syntax_Subst.close tps4 k3
                                             in
                                          let uu____419 =
                                            let uu____424 =
                                              FStar_Syntax_Subst.subst_binders
                                                usubst1 tps4
                                               in
                                            let uu____425 =
                                              let uu____426 =
                                                FStar_Syntax_Subst.shift_subst
                                                  (FStar_List.length tps4)
                                                  usubst1
                                                 in
                                              FStar_Syntax_Subst.subst
                                                uu____426 k4
                                               in
                                            (uu____424, uu____425)  in
                                          match uu____419 with
                                          | (tps5,k5) ->
                                              let fv_tc =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  tc
                                                  FStar_Syntax_Syntax.delta_constant
                                                  FStar_Pervasives_Native.None
                                                 in
                                              let uu____446 =
                                                FStar_TypeChecker_Env.push_let_binding
                                                  env0 (FStar_Util.Inr fv_tc)
                                                  (uvs1, t_tc)
                                                 in
                                              (uu____446,
                                                (let uu___61_452 = s  in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                                        (tc, uvs1, tps5, k5,
                                                          mutuals, data));
                                                   FStar_Syntax_Syntax.sigrng
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigrng);
                                                   FStar_Syntax_Syntax.sigquals
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigquals);
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigmeta);
                                                   FStar_Syntax_Syntax.sigattrs
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigattrs)
                                                 }), u, guard1)))))))))
      | uu____457 -> failwith "impossible"
  
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
            let uu____521 = FStar_Syntax_Subst.univ_var_opening _uvs  in
            (match uu____521 with
             | (usubst,_uvs1) ->
                 let uu____544 =
                   let uu____549 =
                     FStar_TypeChecker_Env.push_univ_vars env _uvs1  in
                   let uu____550 = FStar_Syntax_Subst.subst usubst t  in
                   (uu____549, uu____550)  in
                 (match uu____544 with
                  | (env1,t1) ->
                      let uu____557 =
                        let tps_u_opt =
                          FStar_Util.find_map tcs
                            (fun uu____596  ->
                               match uu____596 with
                               | (se1,u_tc) ->
                                   let uu____611 =
                                     let uu____613 =
                                       let uu____614 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____614  in
                                     FStar_Ident.lid_equals tc_lid uu____613
                                      in
                                   if uu____611
                                   then
                                     (match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_inductive_typ
                                          (uu____634,uu____635,tps,uu____637,uu____638,uu____639)
                                          ->
                                          let tps1 =
                                            let uu____649 =
                                              FStar_All.pipe_right tps
                                                (FStar_Syntax_Subst.subst_binders
                                                   usubst)
                                               in
                                            FStar_All.pipe_right uu____649
                                              (FStar_List.map
                                                 (fun uu____689  ->
                                                    match uu____689 with
                                                    | (x,uu____703) ->
                                                        (x,
                                                          (FStar_Pervasives_Native.Some
                                                             FStar_Syntax_Syntax.imp_tag))))
                                             in
                                          let tps2 =
                                            FStar_Syntax_Subst.open_binders
                                              tps1
                                             in
                                          let uu____711 =
                                            let uu____718 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 tps2
                                               in
                                            (uu____718, tps2, u_tc)  in
                                          FStar_Pervasives_Native.Some
                                            uu____711
                                      | uu____725 -> failwith "Impossible")
                                   else FStar_Pervasives_Native.None)
                           in
                        match tps_u_opt with
                        | FStar_Pervasives_Native.Some x -> x
                        | FStar_Pervasives_Native.None  ->
                            let uu____768 =
                              FStar_Ident.lid_equals tc_lid
                                FStar_Parser_Const.exn_lid
                               in
                            if uu____768
                            then (env1, [], FStar_Syntax_Syntax.U_zero)
                            else
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                  "Unexpected data constructor")
                                se.FStar_Syntax_Syntax.sigrng
                         in
                      (match uu____557 with
                       | (env2,tps,u_tc) ->
                           let uu____800 =
                             let t2 =
                               FStar_TypeChecker_Normalize.normalize
                                 (FStar_List.append
                                    FStar_TypeChecker_Normalize.whnf_steps
                                    [FStar_TypeChecker_Env.AllowUnboundUniverses])
                                 env2 t1
                                in
                             let uu____816 =
                               let uu____817 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____817.FStar_Syntax_Syntax.n  in
                             match uu____816 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____856 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____856 with
                                  | (uu____897,bs') ->
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
                                                fun uu____968  ->
                                                  match uu____968 with
                                                  | (x,uu____977) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            ((Prims.parse_int "1")
                                                               + i)), x)))
                                         in
                                      let uu____984 =
                                        FStar_Syntax_Subst.subst subst1 t3
                                         in
                                      FStar_Syntax_Util.arrow_formals
                                        uu____984)
                             | uu____985 -> ([], t2)  in
                           (match uu____800 with
                            | (arguments,result) ->
                                ((let uu____1029 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____1029
                                  then
                                    let uu____1032 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____1034 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____1037 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1032 uu____1034 uu____1037
                                  else ());
                                 (let uu____1042 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____1042 with
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
                                      let uu____1060 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____1060 with
                                       | (result1,res_lcomp) ->
                                           let uu____1071 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____1071 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____1129 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1129
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____1211  ->
                                                      fun uu____1212  ->
                                                        match (uu____1211,
                                                                uu____1212)
                                                        with
                                                        | ((bv,uu____1242),
                                                           (t2,uu____1244))
                                                            ->
                                                            let uu____1271 =
                                                              let uu____1272
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____1272.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____1271
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1276 ->
                                                                 let uu____1277
                                                                   =
                                                                   let uu____1283
                                                                    =
                                                                    let uu____1285
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____1287
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1285
                                                                    uu____1287
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1283)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____1277
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1292 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_Syntax_Syntax.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1292
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____1294 =
                                                     let uu____1295 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____1295.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1294 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1298 -> ()
                                                   | uu____1299 ->
                                                       let uu____1300 =
                                                         let uu____1306 =
                                                           let uu____1308 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____1310 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1308
                                                             uu____1310
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1306)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1300
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1315 =
                                                       let uu____1316 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____1316.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____1315 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1320;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1321;_},tuvs)
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
                                                                    let uu____1335
                                                                    =
                                                                    let uu____1336
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1337
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
                                                                    uu____1336
                                                                    uu____1337
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1335)
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
                                                     | uu____1343 ->
                                                         let uu____1344 =
                                                           let uu____1350 =
                                                             let uu____1352 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____1354 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1352
                                                               uu____1354
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1350)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____1344
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____1372  ->
                                                            fun u_x  ->
                                                              match uu____1372
                                                              with
                                                              | (x,uu____1381)
                                                                  ->
                                                                  let uu____1386
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1386)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____1390 =
                                                       let uu____1399 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1439
                                                                  ->
                                                                 match uu____1439
                                                                 with
                                                                 | (x,uu____1453)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____1399
                                                         arguments1
                                                        in
                                                     let uu____1467 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1390 uu____1467
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___183_1472 = se
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
                                                         (uu___183_1472.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___183_1472.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___183_1472.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___183_1472.FStar_Syntax_Syntax.sigattrs)
                                                     }), g))))))))))))
        | uu____1476 -> failwith "impossible"
  
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
            let uu___191_1543 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (uu___191_1543.FStar_TypeChecker_Env.guard_f);
              FStar_TypeChecker_Env.deferred =
                (uu___191_1543.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (tc_universe_vars,
                  (FStar_Pervasives_Native.snd
                     g.FStar_TypeChecker_Env.univ_ineqs));
              FStar_TypeChecker_Env.implicits =
                (uu___191_1543.FStar_TypeChecker_Env.implicits)
            }  in
          (let uu____1553 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "GenUniverses")
              in
           if uu____1553
           then
             let uu____1558 = FStar_TypeChecker_Rel.guard_to_string env g1
                in
             FStar_Util.print1 "@@@@@@Guard before generalization: %s\n"
               uu____1558
           else ());
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          (let binders =
             FStar_All.pipe_right tcs
               (FStar_List.map
                  (fun uu____1601  ->
                     match uu____1601 with
                     | (se,uu____1607) ->
                         (match se.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_inductive_typ
                              (uu____1608,uu____1609,tps,k,uu____1612,uu____1613)
                              ->
                              let uu____1622 =
                                let uu____1623 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_All.pipe_left
                                  (FStar_Syntax_Util.arrow tps) uu____1623
                                 in
                              FStar_Syntax_Syntax.null_binder uu____1622
                          | uu____1628 -> failwith "Impossible")))
              in
           let binders' =
             FStar_All.pipe_right datas
               (FStar_List.map
                  (fun se  ->
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_datacon
                         (uu____1657,uu____1658,t,uu____1660,uu____1661,uu____1662)
                         -> FStar_Syntax_Syntax.null_binder t
                     | uu____1669 -> failwith "Impossible"))
              in
           let t =
             let uu____1674 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
             FStar_Syntax_Util.arrow (FStar_List.append binders binders')
               uu____1674
              in
           (let uu____1684 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "GenUniverses")
               in
            if uu____1684
            then
              let uu____1689 =
                FStar_TypeChecker_Normalize.term_to_string env t  in
              FStar_Util.print1
                "@@@@@@Trying to generalize universes in %s\n" uu____1689
            else ());
           (let uu____1694 =
              FStar_TypeChecker_Util.generalize_universes env t  in
            match uu____1694 with
            | (uvs,t1) ->
                ((let uu____1714 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "GenUniverses")
                     in
                  if uu____1714
                  then
                    let uu____1719 =
                      let uu____1721 =
                        FStar_All.pipe_right uvs
                          (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                         in
                      FStar_All.pipe_right uu____1721
                        (FStar_String.concat ", ")
                       in
                    let uu____1738 = FStar_Syntax_Print.term_to_string t1  in
                    FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                      uu____1719 uu____1738
                  else ());
                 (let uu____1743 = FStar_Syntax_Subst.open_univ_vars uvs t1
                     in
                  match uu____1743 with
                  | (uvs1,t2) ->
                      let uu____1758 = FStar_Syntax_Util.arrow_formals t2  in
                      (match uu____1758 with
                       | (args,uu____1782) ->
                           let uu____1803 =
                             FStar_Util.first_N (FStar_List.length binders)
                               args
                              in
                           (match uu____1803 with
                            | (tc_types,data_types) ->
                                let tcs1 =
                                  FStar_List.map2
                                    (fun uu____1908  ->
                                       fun uu____1909  ->
                                         match (uu____1908, uu____1909) with
                                         | ((x,uu____1931),(se,uu____1933))
                                             ->
                                             (match se.FStar_Syntax_Syntax.sigel
                                              with
                                              | FStar_Syntax_Syntax.Sig_inductive_typ
                                                  (tc,uu____1949,tps,uu____1951,mutuals,datas1)
                                                  ->
                                                  let ty =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs1
                                                      x.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____1963 =
                                                    let uu____1968 =
                                                      let uu____1969 =
                                                        FStar_Syntax_Subst.compress
                                                          ty
                                                         in
                                                      uu____1969.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____1968 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (binders1,c) ->
                                                        let uu____1998 =
                                                          FStar_Util.first_N
                                                            (FStar_List.length
                                                               tps) binders1
                                                           in
                                                        (match uu____1998
                                                         with
                                                         | (tps1,rest) ->
                                                             let t3 =
                                                               match rest
                                                               with
                                                               | [] ->
                                                                   FStar_Syntax_Util.comp_result
                                                                    c
                                                               | uu____2076
                                                                   ->
                                                                   FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                    FStar_Pervasives_Native.None
                                                                    (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                                in
                                                             (tps1, t3))
                                                    | uu____2095 -> ([], ty)
                                                     in
                                                  (match uu____1963 with
                                                   | (tps1,t3) ->
                                                       let uu___268_2104 = se
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
                                                           (uu___268_2104.FStar_Syntax_Syntax.sigrng);
                                                         FStar_Syntax_Syntax.sigquals
                                                           =
                                                           (uu___268_2104.FStar_Syntax_Syntax.sigquals);
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           (uu___268_2104.FStar_Syntax_Syntax.sigmeta);
                                                         FStar_Syntax_Syntax.sigattrs
                                                           =
                                                           (uu___268_2104.FStar_Syntax_Syntax.sigattrs)
                                                       })
                                              | uu____2109 ->
                                                  failwith "Impossible"))
                                    tc_types tcs
                                   in
                                let datas1 =
                                  match uvs1 with
                                  | [] -> datas
                                  | uu____2116 ->
                                      let uvs_universes =
                                        FStar_All.pipe_right uvs1
                                          (FStar_List.map
                                             (fun _2120  ->
                                                FStar_Syntax_Syntax.U_name
                                                  _2120))
                                         in
                                      let tc_insts =
                                        FStar_All.pipe_right tcs1
                                          (FStar_List.map
                                             (fun uu___0_2139  ->
                                                match uu___0_2139 with
                                                | {
                                                    FStar_Syntax_Syntax.sigel
                                                      =
                                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                                      (tc,uu____2145,uu____2146,uu____2147,uu____2148,uu____2149);
                                                    FStar_Syntax_Syntax.sigrng
                                                      = uu____2150;
                                                    FStar_Syntax_Syntax.sigquals
                                                      = uu____2151;
                                                    FStar_Syntax_Syntax.sigmeta
                                                      = uu____2152;
                                                    FStar_Syntax_Syntax.sigattrs
                                                      = uu____2153;_}
                                                    -> (tc, uvs_universes)
                                                | uu____2166 ->
                                                    failwith "Impossible"))
                                         in
                                      FStar_List.map2
                                        (fun uu____2190  ->
                                           fun d  ->
                                             match uu____2190 with
                                             | (t3,uu____2199) ->
                                                 (match d.FStar_Syntax_Syntax.sigel
                                                  with
                                                  | FStar_Syntax_Syntax.Sig_datacon
                                                      (l,uu____2205,uu____2206,tc,ntps,mutuals)
                                                      ->
                                                      let ty =
                                                        let uu____2217 =
                                                          FStar_Syntax_InstFV.instantiate
                                                            tc_insts
                                                            t3.FStar_Syntax_Syntax.sort
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2217
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             uvs1)
                                                         in
                                                      let uu___304_2218 = d
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
                                                          (uu___304_2218.FStar_Syntax_Syntax.sigrng);
                                                        FStar_Syntax_Syntax.sigquals
                                                          =
                                                          (uu___304_2218.FStar_Syntax_Syntax.sigquals);
                                                        FStar_Syntax_Syntax.sigmeta
                                                          =
                                                          (uu___304_2218.FStar_Syntax_Syntax.sigmeta);
                                                        FStar_Syntax_Syntax.sigattrs
                                                          =
                                                          (uu___304_2218.FStar_Syntax_Syntax.sigattrs)
                                                      }
                                                  | uu____2222 ->
                                                      failwith "Impossible"))
                                        data_types datas
                                   in
                                (tcs1, datas1)))))))
  
let (debug_log : FStar_TypeChecker_Env.env_t -> Prims.string -> unit) =
  fun env  ->
    fun s  ->
      let uu____2241 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2241
      then
        FStar_Util.print_string
          (Prims.op_Hat "Positivity::" (Prims.op_Hat s "\n"))
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2263 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2263
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____2280 =
      let uu____2281 = FStar_Syntax_Subst.compress t  in
      uu____2281.FStar_Syntax_Syntax.n  in
    match uu____2280 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2300 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2306 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____2343 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2392  ->
               match uu____2392 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2436 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2436  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2343
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          (let uu____2641 =
             let uu____2643 = FStar_Syntax_Print.term_to_string btype  in
             Prims.op_Hat "Checking strict positivity in type: " uu____2643
              in
           debug_log env uu____2641);
          (let btype1 =
             FStar_TypeChecker_Normalize.normalize
               [FStar_TypeChecker_Env.Beta;
               FStar_TypeChecker_Env.UnfoldUntil
                 FStar_Syntax_Syntax.delta_constant;
               FStar_TypeChecker_Env.Iota;
               FStar_TypeChecker_Env.Zeta;
               FStar_TypeChecker_Env.AllowUnboundUniverses] env btype
              in
           (let uu____2648 =
              let uu____2650 = FStar_Syntax_Print.term_to_string btype1  in
              Prims.op_Hat
                "Checking strict positivity in type, after normalization: "
                uu____2650
               in
            debug_log env uu____2648);
           (let uu____2655 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2655) ||
             ((debug_log env "ty does occur in this type, pressing ahead";
               (let uu____2668 =
                  let uu____2669 = FStar_Syntax_Subst.compress btype1  in
                  uu____2669.FStar_Syntax_Syntax.n  in
                match uu____2668 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2699 = try_get_fv t  in
                    (match uu____2699 with
                     | (fv,us) ->
                         let uu____2707 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2707
                         then
                           (debug_log env
                              "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments";
                            FStar_List.for_all
                              (fun uu____2723  ->
                                 match uu____2723 with
                                 | (t1,uu____2732) ->
                                     let uu____2737 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2737) args)
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
                          let uu____2772 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2772
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2776 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2776
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
                            (fun uu____2803  ->
                               match uu____2803 with
                               | (b,uu____2812) ->
                                   let uu____2817 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2817) sbs)
                           &&
                           ((let uu____2823 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2823 with
                             | (uu____2829,return_type) ->
                                 let uu____2831 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2831)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2832 ->
                    (debug_log env
                       "Checking strict positivity in an fvar, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2836 ->
                    (debug_log env
                       "Checking strict positivity in an Tm_type, return true";
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2841) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2849) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_refine, recur in the bv sort)";
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2856,branches) ->
                    (debug_log env
                       "Checking strict positivity in an Tm_match, recur in the branches)";
                     FStar_List.for_all
                       (fun uu____2915  ->
                          match uu____2915 with
                          | (p,uu____2928,t) ->
                              let bs =
                                let uu____2947 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2947
                                 in
                              let uu____2956 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2956 with
                               | (bs1,t1) ->
                                   let uu____2964 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2964)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2966,uu____2967)
                    ->
                    (debug_log env
                       "Checking strict positivity in an Tm_ascribed, recur)";
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____3010 ->
                    ((let uu____3012 =
                        let uu____3014 =
                          let uu____3016 =
                            FStar_Syntax_Print.tag_of_term btype1  in
                          let uu____3018 =
                            let uu____3020 =
                              FStar_Syntax_Print.term_to_string btype1  in
                            Prims.op_Hat " and term: " uu____3020  in
                          Prims.op_Hat uu____3016 uu____3018  in
                        Prims.op_Hat
                          "Checking strict positivity, unexpected tag: "
                          uu____3014
                         in
                      debug_log env uu____3012);
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
              (let uu____3033 =
                 let uu____3035 =
                   let uu____3037 =
                     let uu____3039 = FStar_Syntax_Print.args_to_string args
                        in
                     Prims.op_Hat " applied to arguments: " uu____3039  in
                   Prims.op_Hat ilid.FStar_Ident.str uu____3037  in
                 Prims.op_Hat "Checking nested positivity in the inductive "
                   uu____3035
                  in
               debug_log env uu____3033);
              (let uu____3043 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3043 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3062 =
                       let uu____3064 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3064
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____3062
                      then
                        ((let uu____3068 =
                            let uu____3070 = FStar_Ident.string_of_lid ilid
                               in
                            FStar_Util.format1
                              "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                              uu____3070
                             in
                          debug_log env uu____3068);
                         true)
                      else
                        (debug_log env
                           "Checking nested positivity, not an inductive, return false";
                         false))
                   else
                     (let uu____3081 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3081
                      then
                        (debug_log env
                           "Checking nested positivity, we have already unfolded this inductive with these args";
                         true)
                      else
                        (let num_ibs =
                           let uu____3092 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3092  in
                         (let uu____3098 =
                            let uu____3100 =
                              let uu____3102 =
                                FStar_Util.string_of_int num_ibs  in
                              Prims.op_Hat uu____3102
                                ", also adding to the memo table"
                               in
                            Prims.op_Hat
                              "Checking nested positivity, number of type parameters is "
                              uu____3100
                             in
                          debug_log env uu____3098);
                         (let uu____3107 =
                            let uu____3108 = FStar_ST.op_Bang unfolded  in
                            let uu____3134 =
                              let uu____3141 =
                                let uu____3146 =
                                  let uu____3147 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3147  in
                                (ilid, uu____3146)  in
                              [uu____3141]  in
                            FStar_List.append uu____3108 uu____3134  in
                          FStar_ST.op_Colon_Equals unfolded uu____3107);
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
                  (let uu____3246 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3246 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3269 ->
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
                         (let uu____3273 =
                            let uu____3275 =
                              FStar_Syntax_Print.term_to_string dt1  in
                            Prims.op_Hat
                              "Checking nested positivity in the data constructor type: "
                              uu____3275
                             in
                          debug_log env uu____3273);
                         (let uu____3278 =
                            let uu____3279 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3279.FStar_Syntax_Syntax.n  in
                          match uu____3278 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 "Checked nested positivity in Tm_arrow data constructor type";
                               (let uu____3307 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3307 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3371 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3371 dbs1
                                       in
                                    let c1 =
                                      let uu____3375 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3375 c
                                       in
                                    let uu____3378 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3378 with
                                     | (args1,uu____3413) ->
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
                                           let uu____3505 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3505 c1
                                            in
                                         ((let uu____3515 =
                                             let uu____3517 =
                                               let uu____3519 =
                                                 FStar_Syntax_Print.binders_to_string
                                                   "; " dbs3
                                                  in
                                               let uu____3522 =
                                                 let uu____3524 =
                                                   FStar_Syntax_Print.comp_to_string
                                                     c2
                                                    in
                                                 Prims.op_Hat ", and c: "
                                                   uu____3524
                                                  in
                                               Prims.op_Hat uu____3519
                                                 uu____3522
                                                in
                                             Prims.op_Hat
                                               "Checking nested positivity in the unfolded data constructor binders as: "
                                               uu____3517
                                              in
                                           debug_log env uu____3515);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3538 ->
                              (debug_log env
                                 "Checking nested positivity in the data constructor type that is not an arrow";
                               (let uu____3541 =
                                  let uu____3542 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3542.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3541
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
                   (let uu____3581 = try_get_fv t1  in
                    match uu____3581 with
                    | (fv,uu____3588) ->
                        let uu____3589 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3589
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  ((let uu____3621 =
                      let uu____3623 =
                        FStar_Syntax_Print.binders_to_string "; " sbs  in
                      Prims.op_Hat
                        "Checking nested positivity in an Tm_arrow node, with binders as: "
                        uu____3623
                       in
                    debug_log env uu____3621);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3628 =
                      FStar_List.fold_left
                        (fun uu____3649  ->
                           fun b  ->
                             match uu____3649 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3680 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3684 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3680, uu____3684))) (true, env)
                        sbs1
                       in
                    match uu____3628 with | (b,uu____3702) -> b))
              | uu____3705 ->
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
              let uu____3741 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3741 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3764 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   (let uu____3767 =
                      let uu____3769 = FStar_Syntax_Print.term_to_string dt
                         in
                      Prims.op_Hat "Checking data constructor type: "
                        uu____3769
                       in
                    debug_log env uu____3767);
                   (let uu____3772 =
                      let uu____3773 = FStar_Syntax_Subst.compress dt  in
                      uu____3773.FStar_Syntax_Syntax.n  in
                    match uu____3772 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3777 ->
                        (debug_log env
                           "Data constructor type is simply an fvar, returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3782) ->
                        let dbs1 =
                          let uu____3812 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3812  in
                        let dbs2 =
                          let uu____3862 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3862 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        ((let uu____3867 =
                            let uu____3869 =
                              let uu____3871 =
                                FStar_Util.string_of_int
                                  (FStar_List.length dbs3)
                                 in
                              Prims.op_Hat uu____3871 " binders"  in
                            Prims.op_Hat
                              "Data constructor type is an arrow type, so checking strict positivity in "
                              uu____3869
                             in
                          debug_log env uu____3867);
                         (let uu____3881 =
                            FStar_List.fold_left
                              (fun uu____3902  ->
                                 fun b  ->
                                   match uu____3902 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3933 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3937 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3933, uu____3937)))
                              (true, env) dbs3
                             in
                          match uu____3881 with | (b,uu____3955) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3958,uu____3959) ->
                        (debug_log env
                           "Data constructor type is a Tm_app, so returning true";
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           "Data constructor type is a Tm_uinst, so recursing in the base type";
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____3995 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____4018 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4034,uu____4035,uu____4036) -> (lid, us, bs)
        | uu____4045 -> failwith "Impossible!"  in
      match uu____4018 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4057 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4057 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4081 =
                 let uu____4084 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4084  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4098 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4098
                      unfolded_inductives env2) uu____4081)
  
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
        (uu____4133,uu____4134,t,uu____4136,uu____4137,uu____4138) -> t
    | uu____4145 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4162 =
         let uu____4164 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4164 haseq_suffix  in
       uu____4162 = (Prims.parse_int "0"))
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4174 =
      let uu____4177 =
        let uu____4180 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4180]  in
      FStar_List.append lid.FStar_Ident.ns uu____4177  in
    FStar_Ident.lid_of_ids uu____4174
  
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
          let uu____4226 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4240,bs,t,uu____4243,uu____4244) -> (lid, bs, t)
            | uu____4253 -> failwith "Impossible!"  in
          match uu____4226 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4276 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4276 t  in
              let uu____4285 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4285 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4303 =
                       let uu____4304 = FStar_Syntax_Subst.compress t2  in
                       uu____4304.FStar_Syntax_Syntax.n  in
                     match uu____4303 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4308) -> ibs
                     | uu____4329 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4338 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4339 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4338 uu____4339
                      in
                   let ind1 =
                     let uu____4345 =
                       let uu____4350 =
                         FStar_List.map
                           (fun uu____4367  ->
                              match uu____4367 with
                              | (bv,aq) ->
                                  let uu____4386 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4386, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4350  in
                     uu____4345 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4392 =
                       let uu____4397 =
                         FStar_List.map
                           (fun uu____4414  ->
                              match uu____4414 with
                              | (bv,aq) ->
                                  let uu____4433 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4433, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4397  in
                     uu____4392 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4439 =
                       let uu____4444 =
                         let uu____4445 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4445]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4444
                        in
                     uu____4439 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4494 =
                            let uu____4495 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4495  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4494) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4508 =
                              let uu____4511 =
                                let uu____4516 =
                                  let uu____4517 =
                                    let uu____4526 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4526  in
                                  [uu____4517]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4516
                                 in
                              uu____4511 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4508)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___638_4549 = fml  in
                     let uu____4550 =
                       let uu____4551 =
                         let uu____4558 =
                           let uu____4559 =
                             let uu____4580 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____4585 =
                               let uu____4598 =
                                 let uu____4609 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____4609]  in
                               [uu____4598]  in
                             (uu____4580, uu____4585)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4559  in
                         (fml, uu____4558)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4551  in
                     {
                       FStar_Syntax_Syntax.n = uu____4550;
                       FStar_Syntax_Syntax.pos =
                         (uu___638_4549.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___638_4549.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4678 =
                              let uu____4683 =
                                let uu____4684 =
                                  let uu____4693 =
                                    let uu____4694 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4694 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4693  in
                                [uu____4684]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4683
                               in
                            uu____4678 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4747 =
                              let uu____4752 =
                                let uu____4753 =
                                  let uu____4762 =
                                    let uu____4763 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4763 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4762  in
                                [uu____4753]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4752
                               in
                            uu____4747 FStar_Pervasives_Native.None
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
          let uu____4838 =
            let uu____4839 = FStar_Syntax_Subst.compress dt1  in
            uu____4839.FStar_Syntax_Syntax.n  in
          match uu____4838 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4843) ->
              let dbs1 =
                let uu____4873 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4873  in
              let dbs2 =
                let uu____4923 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4923 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4938 =
                           let uu____4943 =
                             let uu____4944 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4944]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4943
                            in
                         uu____4938 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____4975 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____4975 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____4983 =
                       let uu____4988 =
                         let uu____4989 =
                           let uu____4998 =
                             let uu____4999 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____4999
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____4998  in
                         [uu____4989]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____4988
                        in
                     uu____4983 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5046 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5137,uu____5138,uu____5139,uu____5140,uu____5141)
                  -> lid
              | uu____5150 -> failwith "Impossible!"  in
            let uu____5152 = acc  in
            match uu____5152 with
            | (uu____5189,en,uu____5191,uu____5192) ->
                let uu____5213 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5213 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5250 = acc  in
                     (match uu____5250 with
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
                                     (uu____5325,uu____5326,uu____5327,t_lid,uu____5329,uu____5330)
                                     -> t_lid = lid
                                 | uu____5337 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5352 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5352)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5355 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5358 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5355, uu____5358)))
  
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
          let uu____5416 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5426,us,uu____5428,t,uu____5430,uu____5431) -> 
                (us, t)
            | uu____5440 -> failwith "Impossible!"  in
          match uu____5416 with
          | (us,t) ->
              let uu____5450 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5450 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5476 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5476 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5554 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5554 with
                           | (uu____5569,t1) ->
                               let uu____5591 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5591
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5596 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5596 with
                          | (phi1,uu____5604) ->
                              ((let uu____5606 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5606
                                then
                                  let uu____5609 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5609
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5627  ->
                                         match uu____5627 with
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
                let uu____5699 =
                  let uu____5700 = FStar_Syntax_Subst.compress t  in
                  uu____5700.FStar_Syntax_Syntax.n  in
                match uu____5699 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5708) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5745 = is_mutual t'  in
                    if uu____5745
                    then true
                    else
                      (let uu____5752 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5752)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5772) -> is_mutual t'
                | uu____5777 -> false
              
              and exists_mutual uu___1_5779 =
                match uu___1_5779 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5800 =
                let uu____5801 = FStar_Syntax_Subst.compress dt1  in
                uu____5801.FStar_Syntax_Syntax.n  in
              match uu____5800 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5807) ->
                  let dbs1 =
                    let uu____5837 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5837  in
                  let dbs2 =
                    let uu____5887 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5887 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5907 =
                               let uu____5912 =
                                 let uu____5913 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5913]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5912
                                in
                             uu____5907 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5943 = is_mutual sort  in
                             if uu____5943
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
                           let uu____5956 =
                             let uu____5961 =
                               let uu____5962 =
                                 let uu____5971 =
                                   let uu____5972 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____5972 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____5971  in
                               [uu____5962]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5961
                              in
                           uu____5956 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____6019 -> acc
  
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
              let uu____6069 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6091,bs,t,uu____6094,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6106 -> failwith "Impossible!"  in
              match uu____6069 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6130 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6130 t  in
                  let uu____6139 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6139 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6149 =
                           let uu____6150 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6150.FStar_Syntax_Syntax.n  in
                         match uu____6149 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6154) ->
                             ibs
                         | uu____6175 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6184 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6185 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6184
                           uu____6185
                          in
                       let ind1 =
                         let uu____6191 =
                           let uu____6196 =
                             FStar_List.map
                               (fun uu____6213  ->
                                  match uu____6213 with
                                  | (bv,aq) ->
                                      let uu____6232 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6232, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6196  in
                         uu____6191 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6238 =
                           let uu____6243 =
                             FStar_List.map
                               (fun uu____6260  ->
                                  match uu____6260 with
                                  | (bv,aq) ->
                                      let uu____6279 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6279, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6243  in
                         uu____6238 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6285 =
                           let uu____6290 =
                             let uu____6291 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6291]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6290
                            in
                         uu____6285 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6328,uu____6329,uu____6330,t_lid,uu____6332,uu____6333)
                                  -> t_lid = lid
                              | uu____6340 -> failwith "Impossible")
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
                         let uu___875_6352 = fml  in
                         let uu____6353 =
                           let uu____6354 =
                             let uu____6361 =
                               let uu____6362 =
                                 let uu____6383 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____6388 =
                                   let uu____6401 =
                                     let uu____6412 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____6412]  in
                                   [uu____6401]  in
                                 (uu____6383, uu____6388)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6362
                                in
                             (fml, uu____6361)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6354  in
                         {
                           FStar_Syntax_Syntax.n = uu____6353;
                           FStar_Syntax_Syntax.pos =
                             (uu___875_6352.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___875_6352.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6481 =
                                  let uu____6486 =
                                    let uu____6487 =
                                      let uu____6496 =
                                        let uu____6497 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6497
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6496
                                       in
                                    [uu____6487]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6486
                                   in
                                uu____6481 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6550 =
                                  let uu____6555 =
                                    let uu____6556 =
                                      let uu____6565 =
                                        let uu____6566 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6566
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6565
                                       in
                                    [uu____6556]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6555
                                   in
                                uu____6550 FStar_Pervasives_Native.None
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
                     (lid,uu____6658,uu____6659,uu____6660,uu____6661,uu____6662)
                     -> lid
                 | uu____6671 -> failwith "Impossible!") tcs
             in
          let uu____6673 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6685,uu____6686,uu____6687,uu____6688) ->
                (lid, us)
            | uu____6697 -> failwith "Impossible!"  in
          match uu____6673 with
          | (lid,us) ->
              let uu____6707 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6707 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6734 =
                       let uu____6735 =
                         let uu____6742 = get_haseq_axiom_lid lid  in
                         (uu____6742, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6735  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6734;
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
          let uu____6796 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6821  ->
                    match uu___2_6821 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6823;
                        FStar_Syntax_Syntax.sigrng = uu____6824;
                        FStar_Syntax_Syntax.sigquals = uu____6825;
                        FStar_Syntax_Syntax.sigmeta = uu____6826;
                        FStar_Syntax_Syntax.sigattrs = uu____6827;_} -> true
                    | uu____6849 -> false))
             in
          match uu____6796 with
          | (tys,datas) ->
              ((let uu____6872 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6883  ->
                          match uu___3_6883 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6885;
                              FStar_Syntax_Syntax.sigrng = uu____6886;
                              FStar_Syntax_Syntax.sigquals = uu____6887;
                              FStar_Syntax_Syntax.sigmeta = uu____6888;
                              FStar_Syntax_Syntax.sigattrs = uu____6889;_} ->
                              false
                          | uu____6910 -> true))
                   in
                if uu____6872
                then
                  let uu____6913 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6913
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = (Prims.parse_int "0")
                  then []
                  else
                    (let uu____6928 =
                       let uu____6929 = FStar_List.hd tys  in
                       uu____6929.FStar_Syntax_Syntax.sigel  in
                     match uu____6928 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6932,uvs,uu____6934,uu____6935,uu____6936,uu____6937)
                         -> uvs
                     | uu____6946 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6951 =
                  if (FStar_List.length univs1) = (Prims.parse_int "0")
                  then (env, tys, datas)
                  else
                    (let uu____6981 =
                       FStar_Syntax_Subst.univ_var_opening univs1  in
                     match uu____6981 with
                     | (subst1,univs2) ->
                         let tys1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (lid,uu____7019,bs,t,l1,l2) ->
                                      let uu____7032 =
                                        let uu____7049 =
                                          FStar_Syntax_Subst.subst_binders
                                            subst1 bs
                                           in
                                        let uu____7050 =
                                          let uu____7051 =
                                            FStar_Syntax_Subst.shift_subst
                                              (FStar_List.length bs) subst1
                                             in
                                          FStar_Syntax_Subst.subst uu____7051
                                            t
                                           in
                                        (lid, univs2, uu____7049, uu____7050,
                                          l1, l2)
                                         in
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                        uu____7032
                                  | uu____7064 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___971_7066 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___971_7066.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___971_7066.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___971_7066.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___971_7066.FStar_Syntax_Syntax.sigattrs)
                                }) tys
                            in
                         let datas1 =
                           FStar_List.map
                             (fun se  ->
                                let sigel =
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_datacon
                                      (lid,uu____7076,t,lid_t,x,l) ->
                                      let uu____7087 =
                                        let uu____7103 =
                                          FStar_Syntax_Subst.subst subst1 t
                                           in
                                        (lid, univs2, uu____7103, lid_t, x,
                                          l)
                                         in
                                      FStar_Syntax_Syntax.Sig_datacon
                                        uu____7087
                                  | uu____7107 ->
                                      failwith "Impossible, can't happen"
                                   in
                                let uu___985_7109 = se  in
                                {
                                  FStar_Syntax_Syntax.sigel = sigel;
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___985_7109.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___985_7109.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___985_7109.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___985_7109.FStar_Syntax_Syntax.sigattrs)
                                }) datas
                            in
                         let uu____7110 =
                           FStar_TypeChecker_Env.push_univ_vars env univs2
                            in
                         (uu____7110, tys1, datas1))
                   in
                match uu____6951 with
                | (env1,tys1,datas1) ->
                    let uu____7136 =
                      FStar_List.fold_right
                        (fun tc  ->
                           fun uu____7175  ->
                             match uu____7175 with
                             | (env2,all_tcs,g) ->
                                 let uu____7215 = tc_tycon env2 tc  in
                                 (match uu____7215 with
                                  | (env3,tc1,tc_u,guard) ->
                                      let g' =
                                        FStar_TypeChecker_Rel.universe_inequality
                                          FStar_Syntax_Syntax.U_zero tc_u
                                         in
                                      ((let uu____7242 =
                                          FStar_TypeChecker_Env.debug env3
                                            FStar_Options.Low
                                           in
                                        if uu____7242
                                        then
                                          let uu____7245 =
                                            FStar_Syntax_Print.sigelt_to_string
                                              tc1
                                             in
                                          FStar_Util.print1
                                            "Checked inductive: %s\n"
                                            uu____7245
                                        else ());
                                       (let uu____7250 =
                                          let uu____7251 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard g'
                                             in
                                          FStar_TypeChecker_Env.conj_guard g
                                            uu____7251
                                           in
                                        (env3, ((tc1, tc_u) :: all_tcs),
                                          uu____7250))))) tys1
                        (env1, [], FStar_TypeChecker_Env.trivial_guard)
                       in
                    (match uu____7136 with
                     | (env2,tcs,g) ->
                         let uu____7297 =
                           FStar_List.fold_right
                             (fun se  ->
                                fun uu____7319  ->
                                  match uu____7319 with
                                  | (datas2,g1) ->
                                      let uu____7338 =
                                        let uu____7343 = tc_data env2 tcs  in
                                        uu____7343 se  in
                                      (match uu____7338 with
                                       | (data,g') ->
                                           let uu____7360 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g1 g'
                                              in
                                           ((data :: datas2), uu____7360)))
                             datas1 ([], g)
                            in
                         (match uu____7297 with
                          | (datas2,g1) ->
                              let uu____7381 =
                                if
                                  (FStar_List.length univs1) =
                                    (Prims.parse_int "0")
                                then
                                  generalize_and_inst_within env1 g1 tcs
                                    datas2
                                else
                                  (let uu____7403 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst tcs
                                      in
                                   (uu____7403, datas2))
                                 in
                              (match uu____7381 with
                               | (tcs1,datas3) ->
                                   let sig_bndle =
                                     let uu____7435 =
                                       FStar_TypeChecker_Env.get_range env0
                                        in
                                     let uu____7436 =
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
                                         uu____7435;
                                       FStar_Syntax_Syntax.sigquals = quals;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs =
                                         uu____7436
                                     }  in
                                   (FStar_All.pipe_right tcs1
                                      (FStar_List.iter
                                         (fun se  ->
                                            match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (l,univs2,binders,typ,uu____7462,uu____7463)
                                                ->
                                                let fail1 expected inferred =
                                                  let uu____7483 =
                                                    let uu____7489 =
                                                      let uu____7491 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          expected
                                                         in
                                                      let uu____7493 =
                                                        FStar_Syntax_Print.tscheme_to_string
                                                          inferred
                                                         in
                                                      FStar_Util.format2
                                                        "Expected an inductive with type %s; got %s"
                                                        uu____7491 uu____7493
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                      uu____7489)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____7483
                                                    se.FStar_Syntax_Syntax.sigrng
                                                   in
                                                let uu____7497 =
                                                  FStar_TypeChecker_Env.try_lookup_val_decl
                                                    env0 l
                                                   in
                                                (match uu____7497 with
                                                 | FStar_Pervasives_Native.None
                                                      -> ()
                                                 | FStar_Pervasives_Native.Some
                                                     (expected_typ1,uu____7513)
                                                     ->
                                                     let inferred_typ =
                                                       let body =
                                                         match binders with
                                                         | [] -> typ
                                                         | uu____7544 ->
                                                             let uu____7545 =
                                                               let uu____7552
                                                                 =
                                                                 let uu____7553
                                                                   =
                                                                   let uu____7568
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    typ  in
                                                                   (binders,
                                                                    uu____7568)
                                                                    in
                                                                 FStar_Syntax_Syntax.Tm_arrow
                                                                   uu____7553
                                                                  in
                                                               FStar_Syntax_Syntax.mk
                                                                 uu____7552
                                                                in
                                                             uu____7545
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
                                                       let uu____7590 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           inferred_typ
                                                          in
                                                       (match uu____7590 with
                                                        | (uu____7595,inferred)
                                                            ->
                                                            let uu____7597 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                expected_typ1
                                                               in
                                                            (match uu____7597
                                                             with
                                                             | (uu____7602,expected)
                                                                 ->
                                                                 let uu____7604
                                                                   =
                                                                   FStar_TypeChecker_Rel.teq_nosmt_force
                                                                    env0
                                                                    inferred
                                                                    expected
                                                                    in
                                                                 if
                                                                   uu____7604
                                                                 then ()
                                                                 else
                                                                   fail1
                                                                    expected_typ1
                                                                    inferred_typ))
                                                     else
                                                       fail1 expected_typ1
                                                         inferred_typ)
                                            | uu____7611 -> ()));
                                    (sig_bndle, tcs1, datas3)))))))
  
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"] 
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.attribute Prims.list ->
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
  fun attrs  ->
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
                            let uu____7731 =
                              let uu____7738 =
                                let uu____7739 =
                                  let uu____7746 =
                                    let uu____7749 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7749
                                     in
                                  (uu____7746, inst_univs)  in
                                FStar_Syntax_Syntax.Tm_uinst uu____7739  in
                              FStar_Syntax_Syntax.mk uu____7738  in
                            uu____7731 FStar_Pervasives_Native.None p  in
                          let args =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7783  ->
                                    match uu____7783 with
                                    | (x,imp) ->
                                        let uu____7802 =
                                          FStar_Syntax_Syntax.bv_to_name x
                                           in
                                        (uu____7802, imp)))
                             in
                          FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                            FStar_Pervasives_Native.None p
                           in
                        let unrefined_arg_binder =
                          let uu____7806 = projectee arg_typ  in
                          FStar_Syntax_Syntax.mk_binder uu____7806  in
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
                                 let uu____7829 =
                                   FStar_Ident.set_lid_range disc_name p  in
                                 FStar_Syntax_Syntax.fvar uu____7829
                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                      (Prims.parse_int "1"))
                                   FStar_Pervasives_Native.None
                                  in
                               let uu____7831 =
                                 let uu____7834 =
                                   let uu____7837 =
                                     let uu____7842 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs
                                        in
                                     let uu____7843 =
                                       let uu____7844 =
                                         let uu____7853 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7853
                                          in
                                       [uu____7844]  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7842
                                       uu____7843
                                      in
                                   uu____7837 FStar_Pervasives_Native.None p
                                    in
                                 FStar_Syntax_Util.b2t uu____7834  in
                               FStar_Syntax_Util.refine x uu____7831  in
                             let uu____7878 =
                               let uu___1087_7879 = projectee arg_typ  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1087_7879.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1087_7879.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = sort
                               }  in
                             FStar_Syntax_Syntax.mk_binder uu____7878)
                           in
                        let ntps = FStar_List.length tps  in
                        let all_params =
                          let uu____7896 =
                            FStar_List.map
                              (fun uu____7920  ->
                                 match uu____7920 with
                                 | (x,uu____7934) ->
                                     (x,
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.imp_tag))) tps
                             in
                          FStar_List.append uu____7896 fields  in
                        let imp_binders =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7993  ->
                                  match uu____7993 with
                                  | (x,uu____8007) ->
                                      (x,
                                        (FStar_Pervasives_Native.Some
                                           FStar_Syntax_Syntax.imp_tag))))
                           in
                        let early_prims_inductive =
                          (let uu____8018 =
                             FStar_TypeChecker_Env.current_module env  in
                           FStar_Ident.lid_equals
                             FStar_Parser_Const.prims_lid uu____8018)
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
                                 (let uu____8039 =
                                    let uu____8041 =
                                      FStar_TypeChecker_Env.current_module
                                        env
                                       in
                                    uu____8041.FStar_Ident.str  in
                                  FStar_Options.dont_gen_projectors
                                    uu____8039)
                                in
                             let quals =
                               let uu____8045 =
                                 FStar_List.filter
                                   (fun uu___4_8049  ->
                                      match uu___4_8049 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Inline_for_extraction
                                           -> true
                                      | FStar_Syntax_Syntax.NoExtract  ->
                                          true
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____8054 -> false) iquals
                                  in
                               FStar_List.append
                                 ((FStar_Syntax_Syntax.Discriminator lid) ::
                                 (if only_decl
                                  then
                                    [FStar_Syntax_Syntax.Logic;
                                    FStar_Syntax_Syntax.Assumption]
                                  else [])) uu____8045
                                in
                             let binders =
                               FStar_List.append imp_binders
                                 [unrefined_arg_binder]
                                in
                             let t =
                               let bool_typ =
                                 let uu____8092 =
                                   let uu____8093 =
                                     FStar_Syntax_Syntax.lid_as_fv
                                       FStar_Parser_Const.bool_lid
                                       FStar_Syntax_Syntax.delta_constant
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Syntax_Syntax.fv_to_tm uu____8093
                                    in
                                 FStar_Syntax_Syntax.mk_Total uu____8092  in
                               let uu____8094 =
                                 FStar_Syntax_Util.arrow binders bool_typ  in
                               FStar_All.pipe_left
                                 (FStar_Syntax_Subst.close_univ_vars uvs)
                                 uu____8094
                                in
                             let decl =
                               let uu____8098 =
                                 FStar_Ident.range_of_lid discriminator_name
                                  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (discriminator_name, uvs, t));
                                 FStar_Syntax_Syntax.sigrng = uu____8098;
                                 FStar_Syntax_Syntax.sigquals = quals;
                                 FStar_Syntax_Syntax.sigmeta =
                                   FStar_Syntax_Syntax.default_sigmeta;
                                 FStar_Syntax_Syntax.sigattrs = []
                               }  in
                             (let uu____8100 =
                                FStar_TypeChecker_Env.debug env
                                  (FStar_Options.Other "LogTypes")
                                 in
                              if uu____8100
                              then
                                let uu____8104 =
                                  FStar_Syntax_Print.sigelt_to_string decl
                                   in
                                FStar_Util.print1
                                  "Declaration of a discriminator %s\n"
                                  uu____8104
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
                                               fun uu____8165  ->
                                                 match uu____8165 with
                                                 | (x,imp) ->
                                                     let b =
                                                       FStar_Syntax_Syntax.is_implicit
                                                         imp
                                                        in
                                                     if b && (j < ntps)
                                                     then
                                                       let uu____8190 =
                                                         let uu____8193 =
                                                           let uu____8194 =
                                                             let uu____8201 =
                                                               FStar_Syntax_Syntax.gen_bv
                                                                 (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                 FStar_Pervasives_Native.None
                                                                 FStar_Syntax_Syntax.tun
                                                                in
                                                             (uu____8201,
                                                               FStar_Syntax_Syntax.tun)
                                                              in
                                                           FStar_Syntax_Syntax.Pat_dot_term
                                                             uu____8194
                                                            in
                                                         pos uu____8193  in
                                                       (uu____8190, b)
                                                     else
                                                       (let uu____8209 =
                                                          let uu____8212 =
                                                            let uu____8213 =
                                                              FStar_Syntax_Syntax.gen_bv
                                                                (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                FStar_Pervasives_Native.None
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            FStar_Syntax_Syntax.Pat_wild
                                                              uu____8213
                                                             in
                                                          pos uu____8212  in
                                                        (uu____8209, b))))
                                        in
                                     let pat_true =
                                       let uu____8232 =
                                         let uu____8235 =
                                           let uu____8236 =
                                             let uu____8250 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 lid
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    fvq)
                                                in
                                             (uu____8250, arg_pats)  in
                                           FStar_Syntax_Syntax.Pat_cons
                                             uu____8236
                                            in
                                         pos uu____8235  in
                                       (uu____8232,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_true_bool)
                                        in
                                     let pat_false =
                                       let uu____8285 =
                                         let uu____8288 =
                                           let uu____8289 =
                                             FStar_Syntax_Syntax.new_bv
                                               FStar_Pervasives_Native.None
                                               FStar_Syntax_Syntax.tun
                                              in
                                           FStar_Syntax_Syntax.Pat_wild
                                             uu____8289
                                            in
                                         pos uu____8288  in
                                       (uu____8285,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_false_bool)
                                        in
                                     let arg_exp =
                                       FStar_Syntax_Syntax.bv_to_name
                                         (FStar_Pervasives_Native.fst
                                            unrefined_arg_binder)
                                        in
                                     let uu____8303 =
                                       let uu____8310 =
                                         let uu____8311 =
                                           let uu____8334 =
                                             let uu____8351 =
                                               FStar_Syntax_Util.branch
                                                 pat_true
                                                in
                                             let uu____8366 =
                                               let uu____8383 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false
                                                  in
                                               [uu____8383]  in
                                             uu____8351 :: uu____8366  in
                                           (arg_exp, uu____8334)  in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____8311
                                          in
                                       FStar_Syntax_Syntax.mk uu____8310  in
                                     uu____8303 FStar_Pervasives_Native.None
                                       p)
                                   in
                                let dd =
                                  let uu____8459 =
                                    FStar_All.pipe_right quals
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Abstract)
                                     in
                                  if uu____8459
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
                                  let uu____8481 =
                                    let uu____8486 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        discriminator_name dd
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Util.Inr uu____8486  in
                                  let uu____8487 =
                                    FStar_Syntax_Subst.close_univ_vars uvs
                                      imp
                                     in
                                  FStar_Syntax_Util.mk_letbinding uu____8481
                                    uvs lbtyp
                                    FStar_Parser_Const.effect_Tot_lid
                                    uu____8487 [] FStar_Range.dummyRange
                                   in
                                let impl =
                                  let uu____8493 =
                                    let uu____8494 =
                                      let uu____8501 =
                                        let uu____8504 =
                                          let uu____8505 =
                                            FStar_All.pipe_right
                                              lb.FStar_Syntax_Syntax.lbname
                                              FStar_Util.right
                                             in
                                          FStar_All.pipe_right uu____8505
                                            (fun fv  ->
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                           in
                                        [uu____8504]  in
                                      ((false, [lb]), uu____8501)  in
                                    FStar_Syntax_Syntax.Sig_let uu____8494
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____8493;
                                    FStar_Syntax_Syntax.sigrng = p;
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }  in
                                (let uu____8519 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "LogTypes")
                                    in
                                 if uu____8519
                                 then
                                   let uu____8523 =
                                     FStar_Syntax_Print.sigelt_to_string impl
                                      in
                                   FStar_Util.print1
                                     "Implementation of a discriminator %s\n"
                                     uu____8523
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
                                  fun uu____8596  ->
                                    match uu____8596 with
                                    | (a,uu____8605) ->
                                        let uu____8610 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid a i
                                           in
                                        (match uu____8610 with
                                         | (field_name,uu____8616) ->
                                             let field_proj_tm =
                                               let uu____8618 =
                                                 let uu____8619 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     field_name
                                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                                        (Prims.parse_int "1"))
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____8619
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_uinst
                                                 uu____8618 inst_univs
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
                          let uu____8645 =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i  ->
                                    fun uu____8687  ->
                                      match uu____8687 with
                                      | (x,uu____8698) ->
                                          let p1 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          let uu____8704 =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid x i
                                             in
                                          (match uu____8704 with
                                           | (field_name,uu____8712) ->
                                               let t =
                                                 let uu____8716 =
                                                   let uu____8717 =
                                                     let uu____8720 =
                                                       FStar_Syntax_Subst.subst
                                                         subst1
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Syntax.mk_Total
                                                       uu____8720
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     binders uu____8717
                                                    in
                                                 FStar_All.pipe_left
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      uvs) uu____8716
                                                  in
                                               let only_decl =
                                                 early_prims_inductive ||
                                                   (let uu____8726 =
                                                      let uu____8728 =
                                                        FStar_TypeChecker_Env.current_module
                                                          env
                                                         in
                                                      uu____8728.FStar_Ident.str
                                                       in
                                                    FStar_Options.dont_gen_projectors
                                                      uu____8726)
                                                  in
                                               let no_decl = false  in
                                               let quals q =
                                                 if only_decl
                                                 then
                                                   let uu____8747 =
                                                     FStar_List.filter
                                                       (fun uu___5_8751  ->
                                                          match uu___5_8751
                                                          with
                                                          | FStar_Syntax_Syntax.Abstract
                                                               -> false
                                                          | uu____8754 ->
                                                              true) q
                                                      in
                                                   FStar_Syntax_Syntax.Assumption
                                                     :: uu____8747
                                                 else q  in
                                               let quals1 =
                                                 let iquals1 =
                                                   FStar_All.pipe_right
                                                     iquals
                                                     (FStar_List.filter
                                                        (fun uu___6_8769  ->
                                                           match uu___6_8769
                                                           with
                                                           | FStar_Syntax_Syntax.Inline_for_extraction
                                                                -> true
                                                           | FStar_Syntax_Syntax.NoExtract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Abstract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Private
                                                                -> true
                                                           | uu____8775 ->
                                                               false))
                                                    in
                                                 quals
                                                   ((FStar_Syntax_Syntax.Projector
                                                       (lid,
                                                         (x.FStar_Syntax_Syntax.ppname)))
                                                   :: iquals1)
                                                  in
                                               let attrs1 =
                                                 FStar_List.append
                                                   (if only_decl
                                                    then []
                                                    else
                                                      [FStar_Syntax_Util.attr_substitute])
                                                   attrs
                                                  in
                                               let decl =
                                                 let uu____8786 =
                                                   FStar_Ident.range_of_lid
                                                     field_name
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                                        (field_name, uvs, t));
                                                   FStar_Syntax_Syntax.sigrng
                                                     = uu____8786;
                                                   FStar_Syntax_Syntax.sigquals
                                                     = quals1;
                                                   FStar_Syntax_Syntax.sigmeta
                                                     =
                                                     FStar_Syntax_Syntax.default_sigmeta;
                                                   FStar_Syntax_Syntax.sigattrs
                                                     = attrs1
                                                 }  in
                                               ((let uu____8788 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes")
                                                    in
                                                 if uu____8788
                                                 then
                                                   let uu____8792 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       decl
                                                      in
                                                   FStar_Util.print1
                                                     "Declaration of a projector %s\n"
                                                     uu____8792
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
                                                             fun uu____8846 
                                                               ->
                                                               match uu____8846
                                                               with
                                                               | (x1,imp) ->
                                                                   let b =
                                                                    FStar_Syntax_Syntax.is_implicit
                                                                    imp  in
                                                                   if
                                                                    (i + ntps)
                                                                    = j
                                                                   then
                                                                    let uu____8872
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                    (uu____8872,
                                                                    b)
                                                                   else
                                                                    if
                                                                    b &&
                                                                    (j < ntps)
                                                                    then
                                                                    (let uu____8888
                                                                    =
                                                                    let uu____8891
                                                                    =
                                                                    let uu____8892
                                                                    =
                                                                    let uu____8899
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8899,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8892
                                                                     in
                                                                    pos
                                                                    uu____8891
                                                                     in
                                                                    (uu____8888,
                                                                    b))
                                                                    else
                                                                    (let uu____8907
                                                                    =
                                                                    let uu____8910
                                                                    =
                                                                    let uu____8911
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8911
                                                                     in
                                                                    pos
                                                                    uu____8910
                                                                     in
                                                                    (uu____8907,
                                                                    b))))
                                                      in
                                                   let pat =
                                                     let uu____8930 =
                                                       let uu____8933 =
                                                         let uu____8934 =
                                                           let uu____8948 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               lid
                                                               FStar_Syntax_Syntax.delta_constant
                                                               (FStar_Pervasives_Native.Some
                                                                  fvq)
                                                              in
                                                           (uu____8948,
                                                             arg_pats)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_cons
                                                           uu____8934
                                                          in
                                                       pos uu____8933  in
                                                     let uu____8958 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         projection
                                                        in
                                                     (uu____8930,
                                                       FStar_Pervasives_Native.None,
                                                       uu____8958)
                                                      in
                                                   let body =
                                                     let uu____8974 =
                                                       let uu____8981 =
                                                         let uu____8982 =
                                                           let uu____9005 =
                                                             let uu____9022 =
                                                               FStar_Syntax_Util.branch
                                                                 pat
                                                                in
                                                             [uu____9022]  in
                                                           (arg_exp,
                                                             uu____9005)
                                                            in
                                                         FStar_Syntax_Syntax.Tm_match
                                                           uu____8982
                                                          in
                                                       FStar_Syntax_Syntax.mk
                                                         uu____8981
                                                        in
                                                     uu____8974
                                                       FStar_Pervasives_Native.None
                                                       p1
                                                      in
                                                   let imp =
                                                     FStar_Syntax_Util.abs
                                                       binders body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   let dd =
                                                     let uu____9087 =
                                                       FStar_All.pipe_right
                                                         quals1
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.Abstract)
                                                        in
                                                     if uu____9087
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
                                                     let uu____9106 =
                                                       let uu____9111 =
                                                         FStar_Syntax_Syntax.lid_as_fv
                                                           field_name dd
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       FStar_Util.Inr
                                                         uu____9111
                                                        in
                                                     let uu____9112 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         uvs imp
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.lbname
                                                         = uu____9106;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = lbtyp;
                                                       FStar_Syntax_Syntax.lbeff
                                                         =
                                                         FStar_Parser_Const.effect_Tot_lid;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____9112;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = [];
                                                       FStar_Syntax_Syntax.lbpos
                                                         =
                                                         FStar_Range.dummyRange
                                                     }  in
                                                   let impl =
                                                     let uu____9118 =
                                                       let uu____9119 =
                                                         let uu____9126 =
                                                           let uu____9129 =
                                                             let uu____9130 =
                                                               FStar_All.pipe_right
                                                                 lb.FStar_Syntax_Syntax.lbname
                                                                 FStar_Util.right
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____9130
                                                               (fun fv  ->
                                                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                              in
                                                           [uu____9129]  in
                                                         ((false, [lb]),
                                                           uu____9126)
                                                          in
                                                       FStar_Syntax_Syntax.Sig_let
                                                         uu____9119
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         = uu____9118;
                                                       FStar_Syntax_Syntax.sigrng
                                                         = p1;
                                                       FStar_Syntax_Syntax.sigquals
                                                         = quals1;
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         FStar_Syntax_Syntax.default_sigmeta;
                                                       FStar_Syntax_Syntax.sigattrs
                                                         = attrs1
                                                     }  in
                                                   (let uu____9144 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        (FStar_Options.Other
                                                           "LogTypes")
                                                       in
                                                    if uu____9144
                                                    then
                                                      let uu____9148 =
                                                        FStar_Syntax_Print.sigelt_to_string
                                                          impl
                                                         in
                                                      FStar_Util.print1
                                                        "Implementation of a projector %s\n"
                                                        uu____9148
                                                    else ());
                                                   if no_decl
                                                   then [impl]
                                                   else [decl; impl])))))
                             in
                          FStar_All.pipe_right uu____8645 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____9202) when
              let uu____9209 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____9209 ->
              let uu____9211 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9211 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____9233 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____9233 with
                    | (formals,uu____9251) ->
                        let uu____9272 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____9307 =
                                   let uu____9309 =
                                     let uu____9310 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____9310  in
                                   FStar_Ident.lid_equals typ_lid uu____9309
                                    in
                                 if uu____9307
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9332,uvs',tps,typ0,uu____9336,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              (Prims.parse_int "1")))
                                   | uu____9356 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9405 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9405
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____9272 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9443 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9443 with
                              | (indices,uu____9461) ->
                                  let refine_domain =
                                    let uu____9484 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___7_9491  ->
                                              match uu___7_9491 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9493 -> true
                                              | uu____9503 -> false))
                                       in
                                    if uu____9484
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___8_9518 =
                                      match uu___8_9518 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9521,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9533 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9534 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9534 with
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
                                    let uu____9547 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9547 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9630  ->
                                               fun uu____9631  ->
                                                 match (uu____9630,
                                                         uu____9631)
                                                 with
                                                 | ((x,uu____9657),(x',uu____9659))
                                                     ->
                                                     let uu____9680 =
                                                       let uu____9687 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9687)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9680) imp_tps
                                            inductive_tps1
                                           in
                                        FStar_Syntax_Subst.subst_binders
                                          rename fields
                                     in
                                  mk_discriminator_and_indexed_projectors
                                    se.FStar_Syntax_Syntax.sigattrs iquals1
                                    fv_qual refine_domain env typ_lid
                                    constr_lid uvs1 inductive_tps1 indices
                                    fields))))
          | uu____9692 -> []
  