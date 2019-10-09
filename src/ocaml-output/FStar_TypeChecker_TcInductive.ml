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
        FStar_Syntax_Syntax.universe * FStar_TypeChecker_Common.guard_t))
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
                                              env1 false tps3 guard
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
                                                     (uu___61_452.FStar_Syntax_Syntax.sigattrs);
                                                   FStar_Syntax_Syntax.sigopts
                                                     =
                                                     (uu___61_452.FStar_Syntax_Syntax.sigopts)
                                                 }), u, guard1)))))))))
      | uu____457 -> failwith "impossible"
  
let (tc_data :
  FStar_TypeChecker_Env.env_t ->
    (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universe) Prims.list ->
      FStar_Syntax_Syntax.sigelt ->
        (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Common.guard_t))
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
                                                            (Prims.int_one +
                                                               i)), x)))
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
                                                        res_lcomp.FStar_TypeChecker_Common.res_typ
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
                                                         (uu___183_1472.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___183_1472.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1476 -> failwith "impossible"
  
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
               (fun uu____1567  ->
                  match uu____1567 with
                  | (se,uu____1573) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1574,uu____1575,tps,k,uu____1578,uu____1579)
                           ->
                           let uu____1588 =
                             let uu____1589 = FStar_Syntax_Syntax.mk_Total k
                                in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1589
                              in
                           FStar_Syntax_Syntax.null_binder uu____1588
                       | uu____1594 -> failwith "Impossible")))
           in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1623,uu____1624,t,uu____1626,uu____1627,uu____1628)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1635 -> failwith "Impossible"))
           in
        let t =
          let uu____1640 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1640
           in
        (let uu____1650 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses")
            in
         if uu____1650
         then
           let uu____1655 = FStar_TypeChecker_Normalize.term_to_string env t
              in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1655
         else ());
        (let uu____1660 = FStar_TypeChecker_Util.generalize_universes env t
            in
         match uu____1660 with
         | (uvs,t1) ->
             ((let uu____1680 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses")
                  in
               if uu____1680
               then
                 let uu____1685 =
                   let uu____1687 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                      in
                   FStar_All.pipe_right uu____1687 (FStar_String.concat ", ")
                    in
                 let uu____1704 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1685 uu____1704
               else ());
              (let uu____1709 = FStar_Syntax_Subst.open_univ_vars uvs t1  in
               match uu____1709 with
               | (uvs1,t2) ->
                   let uu____1724 = FStar_Syntax_Util.arrow_formals t2  in
                   (match uu____1724 with
                    | (args,uu____1748) ->
                        let uu____1769 =
                          FStar_Util.first_N (FStar_List.length binders) args
                           in
                        (match uu____1769 with
                         | (tc_types,data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1874  ->
                                    fun uu____1875  ->
                                      match (uu____1874, uu____1875) with
                                      | ((x,uu____1897),(se,uu____1899)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc,uu____1915,tps,uu____1917,mutuals,datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let uu____1929 =
                                                 let uu____1934 =
                                                   let uu____1935 =
                                                     FStar_Syntax_Subst.compress
                                                       ty
                                                      in
                                                   uu____1935.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____1934 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1,c) ->
                                                     let uu____1964 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1
                                                        in
                                                     (match uu____1964 with
                                                      | (tps1,rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____2042 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  FStar_Pervasives_Native.None
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                             in
                                                          (tps1, t3))
                                                 | uu____2061 -> ([], ty)  in
                                               (match uu____1929 with
                                                | (tps1,t3) ->
                                                    let uu___260_2070 = se
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
                                                        (uu___260_2070.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___260_2070.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___260_2070.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___260_2070.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___260_2070.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____2075 ->
                                               failwith "Impossible"))
                                 tc_types tcs
                                in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____2082 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun _2086  ->
                                             FStar_Syntax_Syntax.U_name _2086))
                                      in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_2106  ->
                                             match uu___0_2106 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc,uu____2112,uu____2113,uu____2114,uu____2115,uu____2116);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____2117;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____2118;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____2119;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____2120;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____2121;_}
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
                                                   let uu___297_2188 = d  in
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
                                                       (uu___297_2188.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___297_2188.FStar_Syntax_Syntax.sigopts)
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
       uu____4132 = Prims.int_zero)
  
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
          let uu____6766 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6792  ->
                    match uu___2_6792 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6794;
                        FStar_Syntax_Syntax.sigrng = uu____6795;
                        FStar_Syntax_Syntax.sigquals = uu____6796;
                        FStar_Syntax_Syntax.sigmeta = uu____6797;
                        FStar_Syntax_Syntax.sigattrs = uu____6798;
                        FStar_Syntax_Syntax.sigopts = uu____6799;_} -> true
                    | uu____6823 -> false))
             in
          match uu____6766 with
          | (tys,datas) ->
              ((let uu____6846 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6858  ->
                          match uu___3_6858 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6860;
                              FStar_Syntax_Syntax.sigrng = uu____6861;
                              FStar_Syntax_Syntax.sigquals = uu____6862;
                              FStar_Syntax_Syntax.sigmeta = uu____6863;
                              FStar_Syntax_Syntax.sigattrs = uu____6864;
                              FStar_Syntax_Syntax.sigopts = uu____6865;_} ->
                              false
                          | uu____6888 -> true))
                   in
                if uu____6846
                then
                  let uu____6891 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6891
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6906 =
                       let uu____6907 = FStar_List.hd tys  in
                       uu____6907.FStar_Syntax_Syntax.sigel  in
                     match uu____6906 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6910,uvs,uu____6912,uu____6913,uu____6914,uu____6915)
                         -> uvs
                     | uu____6924 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6929 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____6968  ->
                         match uu____6968 with
                         | (env1,all_tcs,g) ->
                             let uu____7008 = tc_tycon env1 tc  in
                             (match uu____7008 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____7035 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____7035
                                    then
                                      let uu____7038 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____7038
                                    else ());
                                   (let uu____7043 =
                                      let uu____7044 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____7044
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____7043))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard)
                   in
                match uu____6929 with
                | (env1,tcs,g) ->
                    let uu____7090 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____7112  ->
                             match uu____7112 with
                             | (datas1,g1) ->
                                 let uu____7131 =
                                   let uu____7136 = tc_data env1 tcs  in
                                   uu____7136 se  in
                                 (match uu____7131 with
                                  | (data,g') ->
                                      let uu____7153 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____7153))) datas
                        ([], g)
                       in
                    (match uu____7090 with
                     | (datas1,g1) ->
                         let uu____7174 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs
                              in
                           let g2 =
                             let uu___979_7191 = g1  in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___979_7191.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___979_7191.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___979_7191.FStar_TypeChecker_Common.implicits)
                             }  in
                           (let uu____7201 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses")
                               in
                            if uu____7201
                            then
                              let uu____7206 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2
                                 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____7206
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs1) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____7225 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs
                                 in
                              (uu____7225, datas1))
                            in
                         (match uu____7174 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____7257 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                let uu____7258 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses
                                   in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____7257;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____7258;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                }  in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs2,binders,typ,uu____7284,uu____7285)
                                           ->
                                           let fail1 expected inferred =
                                             let uu____7305 =
                                               let uu____7311 =
                                                 let uu____7313 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected
                                                    in
                                                 let uu____7315 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred
                                                    in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____7313 uu____7315
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____7311)
                                                in
                                             FStar_Errors.raise_error
                                               uu____7305
                                               se.FStar_Syntax_Syntax.sigrng
                                              in
                                           let uu____7319 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l
                                              in
                                           (match uu____7319 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1,uu____7335) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____7366 ->
                                                        let uu____7367 =
                                                          let uu____7374 =
                                                            let uu____7375 =
                                                              let uu____7390
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ
                                                                 in
                                                              (binders,
                                                                uu____7390)
                                                               in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____7375
                                                             in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____7374
                                                           in
                                                        uu____7367
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
                                                  let uu____7412 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ
                                                     in
                                                  (match uu____7412 with
                                                   | (uu____7417,inferred) ->
                                                       let uu____7419 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1
                                                          in
                                                       (match uu____7419 with
                                                        | (uu____7424,expected)
                                                            ->
                                                            let uu____7426 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected
                                                               in
                                                            if uu____7426
                                                            then ()
                                                            else
                                                              fail1
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail1 expected_typ1
                                                    inferred_typ)
                                       | uu____7433 -> ()));
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
                            let uu____7551 =
                              let uu____7558 =
                                let uu____7559 =
                                  let uu____7566 =
                                    let uu____7569 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7569
                                     in
                                  (uu____7566, inst_univs)  in
                                FStar_Syntax_Syntax.Tm_uinst uu____7559  in
                              FStar_Syntax_Syntax.mk uu____7558  in
                            uu____7551 FStar_Pervasives_Native.None p  in
                          let args =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7603  ->
                                    match uu____7603 with
                                    | (x,imp) ->
                                        let uu____7622 =
                                          FStar_Syntax_Syntax.bv_to_name x
                                           in
                                        (uu____7622, imp)))
                             in
                          FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                            FStar_Pervasives_Native.None p
                           in
                        let unrefined_arg_binder =
                          let uu____7626 = projectee arg_typ  in
                          FStar_Syntax_Syntax.mk_binder uu____7626  in
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
                                 let uu____7649 =
                                   FStar_Ident.set_lid_range disc_name p  in
                                 FStar_Syntax_Syntax.fvar uu____7649
                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                      Prims.int_one)
                                   FStar_Pervasives_Native.None
                                  in
                               let uu____7651 =
                                 let uu____7654 =
                                   let uu____7657 =
                                     let uu____7662 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs
                                        in
                                     let uu____7663 =
                                       let uu____7664 =
                                         let uu____7673 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7673
                                          in
                                       [uu____7664]  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7662
                                       uu____7663
                                      in
                                   uu____7657 FStar_Pervasives_Native.None p
                                    in
                                 FStar_Syntax_Util.b2t uu____7654  in
                               FStar_Syntax_Util.refine x uu____7651  in
                             let uu____7698 =
                               let uu___1053_7699 = projectee arg_typ  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1053_7699.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1053_7699.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = sort
                               }  in
                             FStar_Syntax_Syntax.mk_binder uu____7698)
                           in
                        let ntps = FStar_List.length tps  in
                        let all_params =
                          let uu____7716 =
                            FStar_List.map
                              (fun uu____7740  ->
                                 match uu____7740 with
                                 | (x,uu____7754) ->
                                     (x,
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.imp_tag))) tps
                             in
                          FStar_List.append uu____7716 fields  in
                        let imp_binders =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7813  ->
                                  match uu____7813 with
                                  | (x,uu____7827) ->
                                      (x,
                                        (FStar_Pervasives_Native.Some
                                           FStar_Syntax_Syntax.imp_tag))))
                           in
                        let early_prims_inductive =
                          (let uu____7838 =
                             FStar_TypeChecker_Env.current_module env  in
                           FStar_Ident.lid_equals
                             FStar_Parser_Const.prims_lid uu____7838)
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
                                 (let uu____7859 =
                                    let uu____7861 =
                                      FStar_TypeChecker_Env.current_module
                                        env
                                       in
                                    uu____7861.FStar_Ident.str  in
                                  FStar_Options.dont_gen_projectors
                                    uu____7859)
                                in
                             let quals =
                               let uu____7865 =
                                 FStar_List.filter
                                   (fun uu___4_7869  ->
                                      match uu___4_7869 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Inline_for_extraction
                                           -> true
                                      | FStar_Syntax_Syntax.NoExtract  ->
                                          true
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7874 -> false) iquals
                                  in
                               FStar_List.append
                                 ((FStar_Syntax_Syntax.Discriminator lid) ::
                                 (if only_decl
                                  then
                                    [FStar_Syntax_Syntax.Logic;
                                    FStar_Syntax_Syntax.Assumption]
                                  else [])) uu____7865
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
                               let uu____7919 =
                                 FStar_Syntax_Util.arrow binders bool_typ  in
                               FStar_All.pipe_left
                                 (FStar_Syntax_Subst.close_univ_vars uvs)
                                 uu____7919
                                in
                             let decl =
                               let uu____7923 =
                                 FStar_Ident.range_of_lid discriminator_name
                                  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (discriminator_name, uvs, t));
                                 FStar_Syntax_Syntax.sigrng = uu____7923;
                                 FStar_Syntax_Syntax.sigquals = quals;
                                 FStar_Syntax_Syntax.sigmeta =
                                   FStar_Syntax_Syntax.default_sigmeta;
                                 FStar_Syntax_Syntax.sigattrs = [];
                                 FStar_Syntax_Syntax.sigopts =
                                   FStar_Pervasives_Native.None
                               }  in
                             (let uu____7925 =
                                FStar_TypeChecker_Env.debug env
                                  (FStar_Options.Other "LogTypes")
                                 in
                              if uu____7925
                              then
                                let uu____7929 =
                                  FStar_Syntax_Print.sigelt_to_string decl
                                   in
                                FStar_Util.print1
                                  "Declaration of a discriminator %s\n"
                                  uu____7929
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
                                               fun uu____7990  ->
                                                 match uu____7990 with
                                                 | (x,imp) ->
                                                     let b =
                                                       FStar_Syntax_Syntax.is_implicit
                                                         imp
                                                        in
                                                     if b && (j < ntps)
                                                     then
                                                       let uu____8015 =
                                                         let uu____8018 =
                                                           let uu____8019 =
                                                             let uu____8026 =
                                                               FStar_Syntax_Syntax.gen_bv
                                                                 (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                 FStar_Pervasives_Native.None
                                                                 FStar_Syntax_Syntax.tun
                                                                in
                                                             (uu____8026,
                                                               FStar_Syntax_Syntax.tun)
                                                              in
                                                           FStar_Syntax_Syntax.Pat_dot_term
                                                             uu____8019
                                                            in
                                                         pos uu____8018  in
                                                       (uu____8015, b)
                                                     else
                                                       (let uu____8034 =
                                                          let uu____8037 =
                                                            let uu____8038 =
                                                              FStar_Syntax_Syntax.gen_bv
                                                                (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                FStar_Pervasives_Native.None
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            FStar_Syntax_Syntax.Pat_wild
                                                              uu____8038
                                                             in
                                                          pos uu____8037  in
                                                        (uu____8034, b))))
                                        in
                                     let pat_true =
                                       let uu____8057 =
                                         let uu____8060 =
                                           let uu____8061 =
                                             let uu____8075 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 lid
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    fvq)
                                                in
                                             (uu____8075, arg_pats)  in
                                           FStar_Syntax_Syntax.Pat_cons
                                             uu____8061
                                            in
                                         pos uu____8060  in
                                       (uu____8057,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_true_bool)
                                        in
                                     let pat_false =
                                       let uu____8110 =
                                         let uu____8113 =
                                           let uu____8114 =
                                             FStar_Syntax_Syntax.new_bv
                                               FStar_Pervasives_Native.None
                                               FStar_Syntax_Syntax.tun
                                              in
                                           FStar_Syntax_Syntax.Pat_wild
                                             uu____8114
                                            in
                                         pos uu____8113  in
                                       (uu____8110,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_false_bool)
                                        in
                                     let arg_exp =
                                       FStar_Syntax_Syntax.bv_to_name
                                         (FStar_Pervasives_Native.fst
                                            unrefined_arg_binder)
                                        in
                                     let uu____8128 =
                                       let uu____8135 =
                                         let uu____8136 =
                                           let uu____8159 =
                                             let uu____8176 =
                                               FStar_Syntax_Util.branch
                                                 pat_true
                                                in
                                             let uu____8191 =
                                               let uu____8208 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false
                                                  in
                                               [uu____8208]  in
                                             uu____8176 :: uu____8191  in
                                           (arg_exp, uu____8159)  in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____8136
                                          in
                                       FStar_Syntax_Syntax.mk uu____8135  in
                                     uu____8128 FStar_Pervasives_Native.None
                                       p)
                                   in
                                let dd =
                                  let uu____8284 =
                                    FStar_All.pipe_right quals
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Abstract)
                                     in
                                  if uu____8284
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
                                  let uu____8306 =
                                    let uu____8311 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        discriminator_name dd
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Util.Inr uu____8311  in
                                  let uu____8312 =
                                    FStar_Syntax_Subst.close_univ_vars uvs
                                      imp
                                     in
                                  FStar_Syntax_Util.mk_letbinding uu____8306
                                    uvs lbtyp
                                    FStar_Parser_Const.effect_Tot_lid
                                    uu____8312 [] FStar_Range.dummyRange
                                   in
                                let impl =
                                  let uu____8318 =
                                    let uu____8319 =
                                      let uu____8326 =
                                        let uu____8329 =
                                          let uu____8330 =
                                            FStar_All.pipe_right
                                              lb.FStar_Syntax_Syntax.lbname
                                              FStar_Util.right
                                             in
                                          FStar_All.pipe_right uu____8330
                                            (fun fv  ->
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                           in
                                        [uu____8329]  in
                                      ((false, [lb]), uu____8326)  in
                                    FStar_Syntax_Syntax.Sig_let uu____8319
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____8318;
                                    FStar_Syntax_Syntax.sigrng = p;
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = [];
                                    FStar_Syntax_Syntax.sigopts =
                                      FStar_Pervasives_Native.None
                                  }  in
                                (let uu____8344 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "LogTypes")
                                    in
                                 if uu____8344
                                 then
                                   let uu____8348 =
                                     FStar_Syntax_Print.sigelt_to_string impl
                                      in
                                   FStar_Util.print1
                                     "Implementation of a discriminator %s\n"
                                     uu____8348
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
                                  fun uu____8421  ->
                                    match uu____8421 with
                                    | (a,uu____8430) ->
                                        let uu____8435 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid a i
                                           in
                                        (match uu____8435 with
                                         | (field_name,uu____8441) ->
                                             let field_proj_tm =
                                               let uu____8443 =
                                                 let uu____8444 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     field_name
                                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                                        Prims.int_one)
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____8444
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_uinst
                                                 uu____8443 inst_univs
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
                          let uu____8470 =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i  ->
                                    fun uu____8512  ->
                                      match uu____8512 with
                                      | (x,uu____8523) ->
                                          let p1 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          let uu____8529 =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid x i
                                             in
                                          (match uu____8529 with
                                           | (field_name,uu____8537) ->
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
                                                 let uu____8550 =
                                                   FStar_Syntax_Util.arrow
                                                     binders result_comp
                                                    in
                                                 FStar_All.pipe_left
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      uvs) uu____8550
                                                  in
                                               let only_decl =
                                                 early_prims_inductive ||
                                                   (let uu____8556 =
                                                      let uu____8558 =
                                                        FStar_TypeChecker_Env.current_module
                                                          env
                                                         in
                                                      uu____8558.FStar_Ident.str
                                                       in
                                                    FStar_Options.dont_gen_projectors
                                                      uu____8556)
                                                  in
                                               let no_decl = false  in
                                               let quals q =
                                                 if only_decl
                                                 then
                                                   let uu____8577 =
                                                     FStar_List.filter
                                                       (fun uu___5_8581  ->
                                                          match uu___5_8581
                                                          with
                                                          | FStar_Syntax_Syntax.Abstract
                                                               -> false
                                                          | uu____8584 ->
                                                              true) q
                                                      in
                                                   FStar_Syntax_Syntax.Assumption
                                                     :: uu____8577
                                                 else q  in
                                               let quals1 =
                                                 let iquals1 =
                                                   FStar_All.pipe_right
                                                     iquals
                                                     (FStar_List.filter
                                                        (fun uu___6_8599  ->
                                                           match uu___6_8599
                                                           with
                                                           | FStar_Syntax_Syntax.Inline_for_extraction
                                                                -> true
                                                           | FStar_Syntax_Syntax.NoExtract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Abstract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Private
                                                                -> true
                                                           | uu____8605 ->
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
                                                 let uu____8616 =
                                                   FStar_Ident.range_of_lid
                                                     field_name
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                                        (field_name, uvs, t));
                                                   FStar_Syntax_Syntax.sigrng
                                                     = uu____8616;
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
                                               ((let uu____8618 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes")
                                                    in
                                                 if uu____8618
                                                 then
                                                   let uu____8622 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       decl
                                                      in
                                                   FStar_Util.print1
                                                     "Declaration of a projector %s\n"
                                                     uu____8622
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
                                                             fun uu____8676 
                                                               ->
                                                               match uu____8676
                                                               with
                                                               | (x1,imp) ->
                                                                   let b =
                                                                    FStar_Syntax_Syntax.is_implicit
                                                                    imp  in
                                                                   if
                                                                    (i + ntps)
                                                                    = j
                                                                   then
                                                                    let uu____8702
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                    (uu____8702,
                                                                    b)
                                                                   else
                                                                    if
                                                                    b &&
                                                                    (j < ntps)
                                                                    then
                                                                    (let uu____8718
                                                                    =
                                                                    let uu____8721
                                                                    =
                                                                    let uu____8722
                                                                    =
                                                                    let uu____8729
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8729,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8722
                                                                     in
                                                                    pos
                                                                    uu____8721
                                                                     in
                                                                    (uu____8718,
                                                                    b))
                                                                    else
                                                                    (let uu____8737
                                                                    =
                                                                    let uu____8740
                                                                    =
                                                                    let uu____8741
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8741
                                                                     in
                                                                    pos
                                                                    uu____8740
                                                                     in
                                                                    (uu____8737,
                                                                    b))))
                                                      in
                                                   let pat =
                                                     let uu____8760 =
                                                       let uu____8763 =
                                                         let uu____8764 =
                                                           let uu____8778 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               lid
                                                               FStar_Syntax_Syntax.delta_constant
                                                               (FStar_Pervasives_Native.Some
                                                                  fvq)
                                                              in
                                                           (uu____8778,
                                                             arg_pats)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_cons
                                                           uu____8764
                                                          in
                                                       pos uu____8763  in
                                                     let uu____8788 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         projection
                                                        in
                                                     (uu____8760,
                                                       FStar_Pervasives_Native.None,
                                                       uu____8788)
                                                      in
                                                   let body =
                                                     let uu____8804 =
                                                       let uu____8811 =
                                                         let uu____8812 =
                                                           let uu____8835 =
                                                             let uu____8852 =
                                                               FStar_Syntax_Util.branch
                                                                 pat
                                                                in
                                                             [uu____8852]  in
                                                           (arg_exp,
                                                             uu____8835)
                                                            in
                                                         FStar_Syntax_Syntax.Tm_match
                                                           uu____8812
                                                          in
                                                       FStar_Syntax_Syntax.mk
                                                         uu____8811
                                                        in
                                                     uu____8804
                                                       FStar_Pervasives_Native.None
                                                       p1
                                                      in
                                                   let imp =
                                                     FStar_Syntax_Util.abs
                                                       binders body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   let dd =
                                                     let uu____8917 =
                                                       FStar_All.pipe_right
                                                         quals1
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.Abstract)
                                                        in
                                                     if uu____8917
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
                                                     let uu____8936 =
                                                       let uu____8941 =
                                                         FStar_Syntax_Syntax.lid_as_fv
                                                           field_name dd
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       FStar_Util.Inr
                                                         uu____8941
                                                        in
                                                     let uu____8942 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         uvs imp
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.lbname
                                                         = uu____8936;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = lbtyp;
                                                       FStar_Syntax_Syntax.lbeff
                                                         =
                                                         FStar_Parser_Const.effect_Tot_lid;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____8942;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = [];
                                                       FStar_Syntax_Syntax.lbpos
                                                         =
                                                         FStar_Range.dummyRange
                                                     }  in
                                                   let impl =
                                                     let uu____8948 =
                                                       let uu____8949 =
                                                         let uu____8956 =
                                                           let uu____8959 =
                                                             let uu____8960 =
                                                               FStar_All.pipe_right
                                                                 lb.FStar_Syntax_Syntax.lbname
                                                                 FStar_Util.right
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____8960
                                                               (fun fv  ->
                                                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                              in
                                                           [uu____8959]  in
                                                         ((false, [lb]),
                                                           uu____8956)
                                                          in
                                                       FStar_Syntax_Syntax.Sig_let
                                                         uu____8949
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         = uu____8948;
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
                                                   (let uu____8974 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        (FStar_Options.Other
                                                           "LogTypes")
                                                       in
                                                    if uu____8974
                                                    then
                                                      let uu____8978 =
                                                        FStar_Syntax_Print.sigelt_to_string
                                                          impl
                                                         in
                                                      FStar_Util.print1
                                                        "Implementation of a projector %s\n"
                                                        uu____8978
                                                    else ());
                                                   if no_decl
                                                   then [impl]
                                                   else [decl; impl])))))
                             in
                          FStar_All.pipe_right uu____8470 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____9032) when
              let uu____9039 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____9039 ->
              let uu____9041 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9041 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____9063 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____9063 with
                    | (formals,uu____9081) ->
                        let uu____9102 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____9137 =
                                   let uu____9139 =
                                     let uu____9140 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____9140  in
                                   FStar_Ident.lid_equals typ_lid uu____9139
                                    in
                                 if uu____9137
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9162,uvs',tps,typ0,uu____9166,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              Prims.int_one))
                                   | uu____9186 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9235 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9235
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____9102 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9273 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9273 with
                              | (indices,uu____9291) ->
                                  let refine_domain =
                                    let uu____9314 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___7_9321  ->
                                              match uu___7_9321 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9323 -> true
                                              | uu____9333 -> false))
                                       in
                                    if uu____9314
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___8_9348 =
                                      match uu___8_9348 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9351,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9363 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9364 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9364 with
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
                                    let uu____9377 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9377 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9460  ->
                                               fun uu____9461  ->
                                                 match (uu____9460,
                                                         uu____9461)
                                                 with
                                                 | ((x,uu____9487),(x',uu____9489))
                                                     ->
                                                     let uu____9510 =
                                                       let uu____9517 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9517)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9510) imp_tps
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
          | uu____9524 -> []
  