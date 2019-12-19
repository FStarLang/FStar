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
  
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env  ->
    fun msg  ->
      let uu____2216 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2216
      then
        let uu____2221 =
          let uu____2223 =
            let uu____2225 = msg ()  in Prims.op_Hat uu____2225 "\n"  in
          Prims.op_Hat "Positivity::" uu____2223  in
        FStar_Util.print_string uu____2221
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2244 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2244
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____2261 =
      let uu____2262 = FStar_Syntax_Subst.compress t  in
      uu____2262.FStar_Syntax_Syntax.n  in
    match uu____2261 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2281 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2287 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____2324 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2373  ->
               match uu____2373 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2417 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2417  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2324
  
let rec (ty_strictly_positive_in_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ty_lid  ->
    fun btype  ->
      fun unfolded  ->
        fun env  ->
          debug_log env
            (fun uu____2624  ->
               let uu____2625 = FStar_Syntax_Print.term_to_string btype  in
               Prims.op_Hat "Checking strict positivity in type: " uu____2625);
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
           debug_log env
             (fun uu____2632  ->
                let uu____2633 = FStar_Syntax_Print.term_to_string btype1  in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu____2633);
           (let uu____2638 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2638) ||
             ((debug_log env
                 (fun uu____2651  ->
                    "ty does occur in this type, pressing ahead");
               (let uu____2653 =
                  let uu____2654 = FStar_Syntax_Subst.compress btype1  in
                  uu____2654.FStar_Syntax_Syntax.n  in
                match uu____2653 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2684 = try_get_fv t  in
                    (match uu____2684 with
                     | (fv,us) ->
                         let uu____2692 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2692
                         then
                           (debug_log env
                              (fun uu____2698  ->
                                 "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                            FStar_List.for_all
                              (fun uu____2710  ->
                                 match uu____2710 with
                                 | (t1,uu____2719) ->
                                     let uu____2724 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2724) args)
                         else
                           (debug_log env
                              (fun uu____2730  ->
                                 "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env
                       (fun uu____2756  ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp1 =
                        let c1 =
                          let uu____2763 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2763
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2767 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2767
                             (FStar_List.existsb
                                (fun q  ->
                                   q = FStar_Syntax_Syntax.TotalEffect)))
                         in
                      if Prims.op_Negation check_comp1
                      then
                        (debug_log env
                           (fun uu____2779  ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu____2786  ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu____2798  ->
                               match uu____2798 with
                               | (b,uu____2807) ->
                                   let uu____2812 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2812) sbs)
                           &&
                           ((let uu____2818 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2818 with
                             | (uu____2824,return_type) ->
                                 let uu____2826 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2826)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2827 ->
                    (debug_log env
                       (fun uu____2830  ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2833 ->
                    (debug_log env
                       (fun uu____2836  ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2840) ->
                    (debug_log env
                       (fun uu____2847  ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2850) ->
                    (debug_log env
                       (fun uu____2857  ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2859,branches) ->
                    (debug_log env
                       (fun uu____2899  ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu____2920  ->
                          match uu____2920 with
                          | (p,uu____2933,t) ->
                              let bs =
                                let uu____2952 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2952
                                 in
                              let uu____2961 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2961 with
                               | (bs1,t1) ->
                                   let uu____2969 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2969)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2971,uu____2972)
                    ->
                    (debug_log env
                       (fun uu____3015  ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____3017 ->
                    (debug_log env
                       (fun uu____3021  ->
                          let uu____3022 =
                            let uu____3024 =
                              FStar_Syntax_Print.tag_of_term btype1  in
                            let uu____3026 =
                              let uu____3028 =
                                FStar_Syntax_Print.term_to_string btype1  in
                              Prims.op_Hat " and term: " uu____3028  in
                            Prims.op_Hat uu____3024 uu____3026  in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu____3022);
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
              debug_log env
                (fun uu____3043  ->
                   let uu____3044 =
                     let uu____3046 =
                       let uu____3048 =
                         FStar_Syntax_Print.args_to_string args  in
                       Prims.op_Hat " applied to arguments: " uu____3048  in
                     Prims.op_Hat ilid.FStar_Ident.str uu____3046  in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive "
                     uu____3044);
              (let uu____3052 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3052 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3071 =
                       let uu____3073 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3073
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____3071
                      then
                        (debug_log env
                           (fun uu____3079  ->
                              let uu____3080 = FStar_Ident.string_of_lid ilid
                                 in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu____3080);
                         true)
                      else
                        (debug_log env
                           (fun uu____3088  ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu____3093 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3093
                      then
                        (debug_log env
                           (fun uu____3099  ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu____3106 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3106  in
                         debug_log env
                           (fun uu____3114  ->
                              let uu____3115 =
                                let uu____3117 =
                                  FStar_Util.string_of_int num_ibs  in
                                Prims.op_Hat uu____3117
                                  ", also adding to the memo table"
                                 in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu____3115);
                         (let uu____3122 =
                            let uu____3123 = FStar_ST.op_Bang unfolded  in
                            let uu____3149 =
                              let uu____3156 =
                                let uu____3161 =
                                  let uu____3162 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3162  in
                                (ilid, uu____3161)  in
                              [uu____3156]  in
                            FStar_List.append uu____3123 uu____3149  in
                          FStar_ST.op_Colon_Equals unfolded uu____3122);
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
                    (fun uu____3260  ->
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         (Prims.op_Hat dlid.FStar_Ident.str
                            (Prims.op_Hat " of the inductive "
                               ilid.FStar_Ident.str)));
                  (let uu____3263 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3263 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3286 ->
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
                         debug_log env
                           (fun uu____3292  ->
                              let uu____3293 =
                                FStar_Syntax_Print.term_to_string dt1  in
                              Prims.op_Hat
                                "Checking nested positivity in the data constructor type: "
                                uu____3293);
                         (let uu____3296 =
                            let uu____3297 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3297.FStar_Syntax_Syntax.n  in
                          match uu____3296 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 (fun uu____3325  ->
                                    "Checked nested positivity in Tm_arrow data constructor type");
                               (let uu____3327 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3327 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3391 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3391 dbs1
                                       in
                                    let c1 =
                                      let uu____3395 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3395 c
                                       in
                                    let uu____3398 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3398 with
                                     | (args1,uu____3433) ->
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
                                           let uu____3525 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3525 c1
                                            in
                                         (debug_log env
                                            (fun uu____3537  ->
                                               let uu____3538 =
                                                 let uu____3540 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     "; " dbs3
                                                    in
                                                 let uu____3543 =
                                                   let uu____3545 =
                                                     FStar_Syntax_Print.comp_to_string
                                                       c2
                                                      in
                                                   Prims.op_Hat ", and c: "
                                                     uu____3545
                                                    in
                                                 Prims.op_Hat uu____3540
                                                   uu____3543
                                                  in
                                               Prims.op_Hat
                                                 "Checking nested positivity in the unfolded data constructor binders as: "
                                                 uu____3538);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3559 ->
                              (debug_log env
                                 (fun uu____3562  ->
                                    "Checking nested positivity in the data constructor type that is not an arrow");
                               (let uu____3564 =
                                  let uu____3565 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3565.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3564
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
                     (fun uu____3604  ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu____3606 = try_get_fv t1  in
                    match uu____3606 with
                    | (fv,uu____3613) ->
                        let uu____3614 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3614
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  (debug_log env
                     (fun uu____3648  ->
                        let uu____3649 =
                          FStar_Syntax_Print.binders_to_string "; " sbs  in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu____3649);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3654 =
                      FStar_List.fold_left
                        (fun uu____3675  ->
                           fun b  ->
                             match uu____3675 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3706 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3710 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3706, uu____3710))) (true, env)
                        sbs1
                       in
                    match uu____3654 with | (b,uu____3728) -> b))
              | uu____3731 ->
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
              let uu____3767 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3767 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3790 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu____3795  ->
                        let uu____3796 = FStar_Syntax_Print.term_to_string dt
                           in
                        Prims.op_Hat "Checking data constructor type: "
                          uu____3796);
                   (let uu____3799 =
                      let uu____3800 = FStar_Syntax_Subst.compress dt  in
                      uu____3800.FStar_Syntax_Syntax.n  in
                    match uu____3799 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3804 ->
                        (debug_log env
                           (fun uu____3807  ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3811) ->
                        let dbs1 =
                          let uu____3841 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3841  in
                        let dbs2 =
                          let uu____3891 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3891 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        (debug_log env
                           (fun uu____3898  ->
                              let uu____3899 =
                                let uu____3901 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3)
                                   in
                                Prims.op_Hat uu____3901 " binders"  in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu____3899);
                         (let uu____3911 =
                            FStar_List.fold_left
                              (fun uu____3932  ->
                                 fun b  ->
                                   match uu____3932 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3963 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3967 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3963, uu____3967)))
                              (true, env) dbs3
                             in
                          match uu____3911 with | (b,uu____3985) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3988,uu____3989) ->
                        (debug_log env
                           (fun uu____4016  ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           (fun uu____4027  ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____4029 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____4052 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4068,uu____4069,uu____4070) -> (lid, us, bs)
        | uu____4079 -> failwith "Impossible!"  in
      match uu____4052 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4091 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4091 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4115 =
                 let uu____4118 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4118  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4132 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4132
                      unfolded_inductives env2) uu____4115)
  
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
        (uu____4167,uu____4168,t,uu____4170,uu____4171,uu____4172) -> t
    | uu____4179 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4196 =
         let uu____4198 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4198 haseq_suffix  in
       uu____4196 = Prims.int_zero)
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4208 =
      let uu____4211 =
        let uu____4214 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4214]  in
      FStar_List.append lid.FStar_Ident.ns uu____4211  in
    FStar_Ident.lid_of_ids uu____4208
  
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
          let uu____4260 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4274,bs,t,uu____4277,uu____4278) -> (lid, bs, t)
            | uu____4287 -> failwith "Impossible!"  in
          match uu____4260 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4310 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4310 t  in
              let uu____4319 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4319 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4337 =
                       let uu____4338 = FStar_Syntax_Subst.compress t2  in
                       uu____4338.FStar_Syntax_Syntax.n  in
                     match uu____4337 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4342) -> ibs
                     | uu____4363 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4372 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4373 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4372 uu____4373
                      in
                   let ind1 =
                     let uu____4379 =
                       let uu____4384 =
                         FStar_List.map
                           (fun uu____4401  ->
                              match uu____4401 with
                              | (bv,aq) ->
                                  let uu____4420 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4420, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4384  in
                     uu____4379 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4426 =
                       let uu____4431 =
                         FStar_List.map
                           (fun uu____4448  ->
                              match uu____4448 with
                              | (bv,aq) ->
                                  let uu____4467 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4467, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4431  in
                     uu____4426 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4473 =
                       let uu____4478 =
                         let uu____4479 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4479]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4478
                        in
                     uu____4473 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4528 =
                            let uu____4529 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4529  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4528) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4542 =
                              let uu____4545 =
                                let uu____4550 =
                                  let uu____4551 =
                                    let uu____4560 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4560  in
                                  [uu____4551]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4550
                                 in
                              uu____4545 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4542)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___663_4583 = fml  in
                     let uu____4584 =
                       let uu____4585 =
                         let uu____4592 =
                           let uu____4593 =
                             let uu____4614 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____4619 =
                               let uu____4632 =
                                 let uu____4643 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____4643]  in
                               [uu____4632]  in
                             (uu____4614, uu____4619)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4593  in
                         (fml, uu____4592)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4585  in
                     {
                       FStar_Syntax_Syntax.n = uu____4584;
                       FStar_Syntax_Syntax.pos =
                         (uu___663_4583.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___663_4583.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4712 =
                              let uu____4717 =
                                let uu____4718 =
                                  let uu____4727 =
                                    let uu____4728 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4728 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4727  in
                                [uu____4718]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4717
                               in
                            uu____4712 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4781 =
                              let uu____4786 =
                                let uu____4787 =
                                  let uu____4796 =
                                    let uu____4797 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4797 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4796  in
                                [uu____4787]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4786
                               in
                            uu____4781 FStar_Pervasives_Native.None
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
          let uu____4872 =
            let uu____4873 = FStar_Syntax_Subst.compress dt1  in
            uu____4873.FStar_Syntax_Syntax.n  in
          match uu____4872 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4877) ->
              let dbs1 =
                let uu____4907 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4907  in
              let dbs2 =
                let uu____4957 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4957 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4972 =
                           let uu____4977 =
                             let uu____4978 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4978]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4977
                            in
                         uu____4972 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____5009 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____5009 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____5017 =
                       let uu____5022 =
                         let uu____5023 =
                           let uu____5032 =
                             let uu____5033 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____5033
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____5032  in
                         [uu____5023]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____5022
                        in
                     uu____5017 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5080 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5171,uu____5172,uu____5173,uu____5174,uu____5175)
                  -> lid
              | uu____5184 -> failwith "Impossible!"  in
            let uu____5186 = acc  in
            match uu____5186 with
            | (uu____5223,en,uu____5225,uu____5226) ->
                let uu____5247 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5247 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5284 = acc  in
                     (match uu____5284 with
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
                                     (uu____5359,uu____5360,uu____5361,t_lid,uu____5363,uu____5364)
                                     -> t_lid = lid
                                 | uu____5371 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5386 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5386)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5389 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5392 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5389, uu____5392)))
  
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
          let uu____5450 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5460,us,uu____5462,t,uu____5464,uu____5465) -> 
                (us, t)
            | uu____5474 -> failwith "Impossible!"  in
          match uu____5450 with
          | (us,t) ->
              let uu____5484 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5484 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5510 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5510 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5588 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5588 with
                           | (uu____5603,t1) ->
                               let uu____5625 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5625
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5630 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5630 with
                          | (phi1,uu____5638) ->
                              ((let uu____5640 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5640
                                then
                                  let uu____5643 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5643
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5661  ->
                                         match uu____5661 with
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
                let uu____5733 =
                  let uu____5734 = FStar_Syntax_Subst.compress t  in
                  uu____5734.FStar_Syntax_Syntax.n  in
                match uu____5733 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5742) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5779 = is_mutual t'  in
                    if uu____5779
                    then true
                    else
                      (let uu____5786 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5786)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5806) -> is_mutual t'
                | uu____5811 -> false
              
              and exists_mutual uu___1_5813 =
                match uu___1_5813 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5834 =
                let uu____5835 = FStar_Syntax_Subst.compress dt1  in
                uu____5835.FStar_Syntax_Syntax.n  in
              match uu____5834 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5841) ->
                  let dbs1 =
                    let uu____5871 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5871  in
                  let dbs2 =
                    let uu____5921 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5921 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5941 =
                               let uu____5946 =
                                 let uu____5947 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5947]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5946
                                in
                             uu____5941 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5977 = is_mutual sort  in
                             if uu____5977
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
                           let uu____5990 =
                             let uu____5995 =
                               let uu____5996 =
                                 let uu____6005 =
                                   let uu____6006 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____6006 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____6005  in
                               [uu____5996]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____5995
                              in
                           uu____5990 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____6053 -> acc
  
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
              let uu____6103 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6125,bs,t,uu____6128,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6140 -> failwith "Impossible!"  in
              match uu____6103 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6164 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6164 t  in
                  let uu____6173 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6173 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6183 =
                           let uu____6184 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6184.FStar_Syntax_Syntax.n  in
                         match uu____6183 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6188) ->
                             ibs
                         | uu____6209 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6218 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6219 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6218
                           uu____6219
                          in
                       let ind1 =
                         let uu____6225 =
                           let uu____6230 =
                             FStar_List.map
                               (fun uu____6247  ->
                                  match uu____6247 with
                                  | (bv,aq) ->
                                      let uu____6266 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6266, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6230  in
                         uu____6225 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6272 =
                           let uu____6277 =
                             FStar_List.map
                               (fun uu____6294  ->
                                  match uu____6294 with
                                  | (bv,aq) ->
                                      let uu____6313 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6313, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6277  in
                         uu____6272 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6319 =
                           let uu____6324 =
                             let uu____6325 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6325]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6324
                            in
                         uu____6319 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6362,uu____6363,uu____6364,t_lid,uu____6366,uu____6367)
                                  -> t_lid = lid
                              | uu____6374 -> failwith "Impossible")
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
                         let uu___900_6386 = fml  in
                         let uu____6387 =
                           let uu____6388 =
                             let uu____6395 =
                               let uu____6396 =
                                 let uu____6417 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____6422 =
                                   let uu____6435 =
                                     let uu____6446 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____6446]  in
                                   [uu____6435]  in
                                 (uu____6417, uu____6422)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6396
                                in
                             (fml, uu____6395)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6388  in
                         {
                           FStar_Syntax_Syntax.n = uu____6387;
                           FStar_Syntax_Syntax.pos =
                             (uu___900_6386.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___900_6386.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6515 =
                                  let uu____6520 =
                                    let uu____6521 =
                                      let uu____6530 =
                                        let uu____6531 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6531
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6530
                                       in
                                    [uu____6521]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6520
                                   in
                                uu____6515 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6584 =
                                  let uu____6589 =
                                    let uu____6590 =
                                      let uu____6599 =
                                        let uu____6600 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6600
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6599
                                       in
                                    [uu____6590]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6589
                                   in
                                uu____6584 FStar_Pervasives_Native.None
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
                     (lid,uu____6692,uu____6693,uu____6694,uu____6695,uu____6696)
                     -> lid
                 | uu____6705 -> failwith "Impossible!") tcs
             in
          let uu____6707 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6719,uu____6720,uu____6721,uu____6722) ->
                (lid, us)
            | uu____6731 -> failwith "Impossible!"  in
          match uu____6707 with
          | (lid,us) ->
              let uu____6741 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6741 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6768 =
                       let uu____6769 =
                         let uu____6776 = get_haseq_axiom_lid lid  in
                         (uu____6776, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6769  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6768;
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
          let uu____6830 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6856  ->
                    match uu___2_6856 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6858;
                        FStar_Syntax_Syntax.sigrng = uu____6859;
                        FStar_Syntax_Syntax.sigquals = uu____6860;
                        FStar_Syntax_Syntax.sigmeta = uu____6861;
                        FStar_Syntax_Syntax.sigattrs = uu____6862;
                        FStar_Syntax_Syntax.sigopts = uu____6863;_} -> true
                    | uu____6887 -> false))
             in
          match uu____6830 with
          | (tys,datas) ->
              ((let uu____6910 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6922  ->
                          match uu___3_6922 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6924;
                              FStar_Syntax_Syntax.sigrng = uu____6925;
                              FStar_Syntax_Syntax.sigquals = uu____6926;
                              FStar_Syntax_Syntax.sigmeta = uu____6927;
                              FStar_Syntax_Syntax.sigattrs = uu____6928;
                              FStar_Syntax_Syntax.sigopts = uu____6929;_} ->
                              false
                          | uu____6952 -> true))
                   in
                if uu____6910
                then
                  let uu____6955 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6955
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6970 =
                       let uu____6971 = FStar_List.hd tys  in
                       uu____6971.FStar_Syntax_Syntax.sigel  in
                     match uu____6970 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6974,uvs,uu____6976,uu____6977,uu____6978,uu____6979)
                         -> uvs
                     | uu____6988 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____6993 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____7032  ->
                         match uu____7032 with
                         | (env1,all_tcs,g) ->
                             let uu____7072 = tc_tycon env1 tc  in
                             (match uu____7072 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____7099 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____7099
                                    then
                                      let uu____7102 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____7102
                                    else ());
                                   (let uu____7107 =
                                      let uu____7108 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____7108
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____7107))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard)
                   in
                match uu____6993 with
                | (env1,tcs,g) ->
                    let uu____7154 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____7176  ->
                             match uu____7176 with
                             | (datas1,g1) ->
                                 let uu____7195 =
                                   let uu____7200 = tc_data env1 tcs  in
                                   uu____7200 se  in
                                 (match uu____7195 with
                                  | (data,g') ->
                                      let uu____7217 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____7217))) datas
                        ([], g)
                       in
                    (match uu____7154 with
                     | (datas1,g1) ->
                         let uu____7238 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs
                              in
                           let g2 =
                             let uu___1011_7255 = g1  in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___1011_7255.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___1011_7255.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___1011_7255.FStar_TypeChecker_Common.implicits)
                             }  in
                           (let uu____7265 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses")
                               in
                            if uu____7265
                            then
                              let uu____7270 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2
                                 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____7270
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs1) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____7289 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs
                                 in
                              (uu____7289, datas1))
                            in
                         (match uu____7238 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____7321 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                let uu____7322 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses
                                   in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____7321;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____7322;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                }  in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs2,binders,typ,uu____7348,uu____7349)
                                           ->
                                           let fail1 expected inferred =
                                             let uu____7369 =
                                               let uu____7375 =
                                                 let uu____7377 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected
                                                    in
                                                 let uu____7379 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred
                                                    in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____7377 uu____7379
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____7375)
                                                in
                                             FStar_Errors.raise_error
                                               uu____7369
                                               se.FStar_Syntax_Syntax.sigrng
                                              in
                                           let uu____7383 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l
                                              in
                                           (match uu____7383 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1,uu____7399) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____7430 ->
                                                        let uu____7431 =
                                                          let uu____7438 =
                                                            let uu____7439 =
                                                              let uu____7454
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ
                                                                 in
                                                              (binders,
                                                                uu____7454)
                                                               in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____7439
                                                             in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____7438
                                                           in
                                                        uu____7431
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
                                                  let uu____7476 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ
                                                     in
                                                  (match uu____7476 with
                                                   | (uu____7481,inferred) ->
                                                       let uu____7483 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1
                                                          in
                                                       (match uu____7483 with
                                                        | (uu____7488,expected)
                                                            ->
                                                            let uu____7490 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected
                                                               in
                                                            if uu____7490
                                                            then ()
                                                            else
                                                              fail1
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail1 expected_typ1
                                                    inferred_typ)
                                       | uu____7497 -> ()));
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
                            let uu____7615 =
                              let uu____7622 =
                                let uu____7623 =
                                  let uu____7630 =
                                    let uu____7633 =
                                      FStar_Syntax_Syntax.lid_as_fv tc
                                        FStar_Syntax_Syntax.delta_constant
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Syntax_Syntax.fv_to_tm uu____7633
                                     in
                                  (uu____7630, inst_univs)  in
                                FStar_Syntax_Syntax.Tm_uinst uu____7623  in
                              FStar_Syntax_Syntax.mk uu____7622  in
                            uu____7615 FStar_Pervasives_Native.None p  in
                          let args =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7667  ->
                                    match uu____7667 with
                                    | (x,imp) ->
                                        let uu____7686 =
                                          FStar_Syntax_Syntax.bv_to_name x
                                           in
                                        (uu____7686, imp)))
                             in
                          FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                            FStar_Pervasives_Native.None p
                           in
                        let unrefined_arg_binder =
                          let uu____7690 = projectee arg_typ  in
                          FStar_Syntax_Syntax.mk_binder uu____7690  in
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
                                 let uu____7713 =
                                   FStar_Ident.set_lid_range disc_name p  in
                                 FStar_Syntax_Syntax.fvar uu____7713
                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                      Prims.int_one)
                                   FStar_Pervasives_Native.None
                                  in
                               let uu____7715 =
                                 let uu____7718 =
                                   let uu____7721 =
                                     let uu____7726 =
                                       FStar_Syntax_Syntax.mk_Tm_uinst
                                         disc_fvar inst_univs
                                        in
                                     let uu____7727 =
                                       let uu____7728 =
                                         let uu____7737 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7737
                                          in
                                       [uu____7728]  in
                                     FStar_Syntax_Syntax.mk_Tm_app uu____7726
                                       uu____7727
                                      in
                                   uu____7721 FStar_Pervasives_Native.None p
                                    in
                                 FStar_Syntax_Util.b2t uu____7718  in
                               FStar_Syntax_Util.refine x uu____7715  in
                             let uu____7762 =
                               let uu___1085_7763 = projectee arg_typ  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1085_7763.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1085_7763.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = sort
                               }  in
                             FStar_Syntax_Syntax.mk_binder uu____7762)
                           in
                        let ntps = FStar_List.length tps  in
                        let all_params =
                          let uu____7780 =
                            FStar_List.map
                              (fun uu____7804  ->
                                 match uu____7804 with
                                 | (x,uu____7818) ->
                                     (x,
                                       (FStar_Pervasives_Native.Some
                                          FStar_Syntax_Syntax.imp_tag))) tps
                             in
                          FStar_List.append uu____7780 fields  in
                        let imp_binders =
                          FStar_All.pipe_right
                            (FStar_List.append tps indices)
                            (FStar_List.map
                               (fun uu____7877  ->
                                  match uu____7877 with
                                  | (x,uu____7891) ->
                                      (x,
                                        (FStar_Pervasives_Native.Some
                                           FStar_Syntax_Syntax.imp_tag))))
                           in
                        let early_prims_inductive =
                          (let uu____7902 =
                             FStar_TypeChecker_Env.current_module env  in
                           FStar_Ident.lid_equals
                             FStar_Parser_Const.prims_lid uu____7902)
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
                                 (let uu____7923 =
                                    let uu____7925 =
                                      FStar_TypeChecker_Env.current_module
                                        env
                                       in
                                    uu____7925.FStar_Ident.str  in
                                  FStar_Options.dont_gen_projectors
                                    uu____7923)
                                in
                             let quals =
                               let uu____7929 =
                                 FStar_List.filter
                                   (fun uu___4_7933  ->
                                      match uu___4_7933 with
                                      | FStar_Syntax_Syntax.Abstract  ->
                                          Prims.op_Negation only_decl
                                      | FStar_Syntax_Syntax.Inline_for_extraction
                                           -> true
                                      | FStar_Syntax_Syntax.NoExtract  ->
                                          true
                                      | FStar_Syntax_Syntax.Private  -> true
                                      | uu____7938 -> false) iquals
                                  in
                               FStar_List.append
                                 ((FStar_Syntax_Syntax.Discriminator lid) ::
                                 (if only_decl
                                  then
                                    [FStar_Syntax_Syntax.Logic;
                                    FStar_Syntax_Syntax.Assumption]
                                  else [])) uu____7929
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
                               let uu____7983 =
                                 FStar_Syntax_Util.arrow binders bool_typ  in
                               FStar_All.pipe_left
                                 (FStar_Syntax_Subst.close_univ_vars uvs)
                                 uu____7983
                                in
                             let decl =
                               let uu____7987 =
                                 FStar_Ident.range_of_lid discriminator_name
                                  in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_declare_typ
                                      (discriminator_name, uvs, t));
                                 FStar_Syntax_Syntax.sigrng = uu____7987;
                                 FStar_Syntax_Syntax.sigquals = quals;
                                 FStar_Syntax_Syntax.sigmeta =
                                   FStar_Syntax_Syntax.default_sigmeta;
                                 FStar_Syntax_Syntax.sigattrs = [];
                                 FStar_Syntax_Syntax.sigopts =
                                   FStar_Pervasives_Native.None
                               }  in
                             (let uu____7989 =
                                FStar_TypeChecker_Env.debug env
                                  (FStar_Options.Other "LogTypes")
                                 in
                              if uu____7989
                              then
                                let uu____7993 =
                                  FStar_Syntax_Print.sigelt_to_string decl
                                   in
                                FStar_Util.print1
                                  "Declaration of a discriminator %s\n"
                                  uu____7993
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
                                               fun uu____8054  ->
                                                 match uu____8054 with
                                                 | (x,imp) ->
                                                     let b =
                                                       FStar_Syntax_Syntax.is_implicit
                                                         imp
                                                        in
                                                     if b && (j < ntps)
                                                     then
                                                       let uu____8079 =
                                                         let uu____8082 =
                                                           let uu____8083 =
                                                             let uu____8090 =
                                                               FStar_Syntax_Syntax.gen_bv
                                                                 (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                 FStar_Pervasives_Native.None
                                                                 FStar_Syntax_Syntax.tun
                                                                in
                                                             (uu____8090,
                                                               FStar_Syntax_Syntax.tun)
                                                              in
                                                           FStar_Syntax_Syntax.Pat_dot_term
                                                             uu____8083
                                                            in
                                                         pos uu____8082  in
                                                       (uu____8079, b)
                                                     else
                                                       (let uu____8098 =
                                                          let uu____8101 =
                                                            let uu____8102 =
                                                              FStar_Syntax_Syntax.gen_bv
                                                                (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                FStar_Pervasives_Native.None
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            FStar_Syntax_Syntax.Pat_wild
                                                              uu____8102
                                                             in
                                                          pos uu____8101  in
                                                        (uu____8098, b))))
                                        in
                                     let pat_true =
                                       let uu____8121 =
                                         let uu____8124 =
                                           let uu____8125 =
                                             let uu____8139 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 lid
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    fvq)
                                                in
                                             (uu____8139, arg_pats)  in
                                           FStar_Syntax_Syntax.Pat_cons
                                             uu____8125
                                            in
                                         pos uu____8124  in
                                       (uu____8121,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_true_bool)
                                        in
                                     let pat_false =
                                       let uu____8174 =
                                         let uu____8177 =
                                           let uu____8178 =
                                             FStar_Syntax_Syntax.new_bv
                                               FStar_Pervasives_Native.None
                                               FStar_Syntax_Syntax.tun
                                              in
                                           FStar_Syntax_Syntax.Pat_wild
                                             uu____8178
                                            in
                                         pos uu____8177  in
                                       (uu____8174,
                                         FStar_Pervasives_Native.None,
                                         FStar_Syntax_Util.exp_false_bool)
                                        in
                                     let arg_exp =
                                       FStar_Syntax_Syntax.bv_to_name
                                         (FStar_Pervasives_Native.fst
                                            unrefined_arg_binder)
                                        in
                                     let uu____8192 =
                                       let uu____8199 =
                                         let uu____8200 =
                                           let uu____8223 =
                                             let uu____8240 =
                                               FStar_Syntax_Util.branch
                                                 pat_true
                                                in
                                             let uu____8255 =
                                               let uu____8272 =
                                                 FStar_Syntax_Util.branch
                                                   pat_false
                                                  in
                                               [uu____8272]  in
                                             uu____8240 :: uu____8255  in
                                           (arg_exp, uu____8223)  in
                                         FStar_Syntax_Syntax.Tm_match
                                           uu____8200
                                          in
                                       FStar_Syntax_Syntax.mk uu____8199  in
                                     uu____8192 FStar_Pervasives_Native.None
                                       p)
                                   in
                                let dd =
                                  let uu____8348 =
                                    FStar_All.pipe_right quals
                                      (FStar_List.contains
                                         FStar_Syntax_Syntax.Abstract)
                                     in
                                  if uu____8348
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
                                  let uu____8370 =
                                    let uu____8375 =
                                      FStar_Syntax_Syntax.lid_as_fv
                                        discriminator_name dd
                                        FStar_Pervasives_Native.None
                                       in
                                    FStar_Util.Inr uu____8375  in
                                  let uu____8376 =
                                    FStar_Syntax_Subst.close_univ_vars uvs
                                      imp
                                     in
                                  FStar_Syntax_Util.mk_letbinding uu____8370
                                    uvs lbtyp
                                    FStar_Parser_Const.effect_Tot_lid
                                    uu____8376 [] FStar_Range.dummyRange
                                   in
                                let impl =
                                  let uu____8382 =
                                    let uu____8383 =
                                      let uu____8390 =
                                        let uu____8393 =
                                          let uu____8394 =
                                            FStar_All.pipe_right
                                              lb.FStar_Syntax_Syntax.lbname
                                              FStar_Util.right
                                             in
                                          FStar_All.pipe_right uu____8394
                                            (fun fv  ->
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                           in
                                        [uu____8393]  in
                                      ((false, [lb]), uu____8390)  in
                                    FStar_Syntax_Syntax.Sig_let uu____8383
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____8382;
                                    FStar_Syntax_Syntax.sigrng = p;
                                    FStar_Syntax_Syntax.sigquals = quals;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = [];
                                    FStar_Syntax_Syntax.sigopts =
                                      FStar_Pervasives_Native.None
                                  }  in
                                (let uu____8408 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "LogTypes")
                                    in
                                 if uu____8408
                                 then
                                   let uu____8412 =
                                     FStar_Syntax_Print.sigelt_to_string impl
                                      in
                                   FStar_Util.print1
                                     "Implementation of a discriminator %s\n"
                                     uu____8412
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
                                  fun uu____8485  ->
                                    match uu____8485 with
                                    | (a,uu____8494) ->
                                        let uu____8499 =
                                          FStar_Syntax_Util.mk_field_projector_name
                                            lid a i
                                           in
                                        (match uu____8499 with
                                         | (field_name,uu____8505) ->
                                             let field_proj_tm =
                                               let uu____8507 =
                                                 let uu____8508 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     field_name
                                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                                        Prims.int_one)
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____8508
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_uinst
                                                 uu____8507 inst_univs
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
                          let uu____8534 =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i  ->
                                    fun uu____8576  ->
                                      match uu____8576 with
                                      | (x,uu____8587) ->
                                          let p1 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          let uu____8593 =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid x i
                                             in
                                          (match uu____8593 with
                                           | (field_name,uu____8601) ->
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
                                                 let uu____8614 =
                                                   FStar_Syntax_Util.arrow
                                                     binders result_comp
                                                    in
                                                 FStar_All.pipe_left
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      uvs) uu____8614
                                                  in
                                               let only_decl =
                                                 early_prims_inductive ||
                                                   (let uu____8620 =
                                                      let uu____8622 =
                                                        FStar_TypeChecker_Env.current_module
                                                          env
                                                         in
                                                      uu____8622.FStar_Ident.str
                                                       in
                                                    FStar_Options.dont_gen_projectors
                                                      uu____8620)
                                                  in
                                               let no_decl = false  in
                                               let quals q =
                                                 if only_decl
                                                 then
                                                   let uu____8641 =
                                                     FStar_List.filter
                                                       (fun uu___5_8645  ->
                                                          match uu___5_8645
                                                          with
                                                          | FStar_Syntax_Syntax.Abstract
                                                               -> false
                                                          | uu____8648 ->
                                                              true) q
                                                      in
                                                   FStar_Syntax_Syntax.Assumption
                                                     :: uu____8641
                                                 else q  in
                                               let quals1 =
                                                 let iquals1 =
                                                   FStar_All.pipe_right
                                                     iquals
                                                     (FStar_List.filter
                                                        (fun uu___6_8663  ->
                                                           match uu___6_8663
                                                           with
                                                           | FStar_Syntax_Syntax.Inline_for_extraction
                                                                -> true
                                                           | FStar_Syntax_Syntax.NoExtract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Abstract
                                                                -> true
                                                           | FStar_Syntax_Syntax.Private
                                                                -> true
                                                           | uu____8669 ->
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
                                                 let uu____8680 =
                                                   FStar_Ident.range_of_lid
                                                     field_name
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.sigel
                                                     =
                                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                                        (field_name, uvs, t));
                                                   FStar_Syntax_Syntax.sigrng
                                                     = uu____8680;
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
                                               ((let uu____8682 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes")
                                                    in
                                                 if uu____8682
                                                 then
                                                   let uu____8686 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       decl
                                                      in
                                                   FStar_Util.print1
                                                     "Declaration of a projector %s\n"
                                                     uu____8686
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
                                                             fun uu____8740 
                                                               ->
                                                               match uu____8740
                                                               with
                                                               | (x1,imp) ->
                                                                   let b =
                                                                    FStar_Syntax_Syntax.is_implicit
                                                                    imp  in
                                                                   if
                                                                    (i + ntps)
                                                                    = j
                                                                   then
                                                                    let uu____8766
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                    (uu____8766,
                                                                    b)
                                                                   else
                                                                    if
                                                                    b &&
                                                                    (j < ntps)
                                                                    then
                                                                    (let uu____8782
                                                                    =
                                                                    let uu____8785
                                                                    =
                                                                    let uu____8786
                                                                    =
                                                                    let uu____8793
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8793,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8786
                                                                     in
                                                                    pos
                                                                    uu____8785
                                                                     in
                                                                    (uu____8782,
                                                                    b))
                                                                    else
                                                                    (let uu____8801
                                                                    =
                                                                    let uu____8804
                                                                    =
                                                                    let uu____8805
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8805
                                                                     in
                                                                    pos
                                                                    uu____8804
                                                                     in
                                                                    (uu____8801,
                                                                    b))))
                                                      in
                                                   let pat =
                                                     let uu____8824 =
                                                       let uu____8827 =
                                                         let uu____8828 =
                                                           let uu____8842 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               lid
                                                               FStar_Syntax_Syntax.delta_constant
                                                               (FStar_Pervasives_Native.Some
                                                                  fvq)
                                                              in
                                                           (uu____8842,
                                                             arg_pats)
                                                            in
                                                         FStar_Syntax_Syntax.Pat_cons
                                                           uu____8828
                                                          in
                                                       pos uu____8827  in
                                                     let uu____8852 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         projection
                                                        in
                                                     (uu____8824,
                                                       FStar_Pervasives_Native.None,
                                                       uu____8852)
                                                      in
                                                   let body =
                                                     let uu____8868 =
                                                       let uu____8875 =
                                                         let uu____8876 =
                                                           let uu____8899 =
                                                             let uu____8916 =
                                                               FStar_Syntax_Util.branch
                                                                 pat
                                                                in
                                                             [uu____8916]  in
                                                           (arg_exp,
                                                             uu____8899)
                                                            in
                                                         FStar_Syntax_Syntax.Tm_match
                                                           uu____8876
                                                          in
                                                       FStar_Syntax_Syntax.mk
                                                         uu____8875
                                                        in
                                                     uu____8868
                                                       FStar_Pervasives_Native.None
                                                       p1
                                                      in
                                                   let imp =
                                                     FStar_Syntax_Util.abs
                                                       binders body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   let dd =
                                                     let uu____8981 =
                                                       FStar_All.pipe_right
                                                         quals1
                                                         (FStar_List.contains
                                                            FStar_Syntax_Syntax.Abstract)
                                                        in
                                                     if uu____8981
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
                                                     let uu____9000 =
                                                       let uu____9005 =
                                                         FStar_Syntax_Syntax.lid_as_fv
                                                           field_name dd
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       FStar_Util.Inr
                                                         uu____9005
                                                        in
                                                     let uu____9006 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         uvs imp
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.lbname
                                                         = uu____9000;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = lbtyp;
                                                       FStar_Syntax_Syntax.lbeff
                                                         =
                                                         FStar_Parser_Const.effect_Tot_lid;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____9006;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = [];
                                                       FStar_Syntax_Syntax.lbpos
                                                         =
                                                         FStar_Range.dummyRange
                                                     }  in
                                                   let impl =
                                                     let uu____9012 =
                                                       let uu____9013 =
                                                         let uu____9020 =
                                                           let uu____9023 =
                                                             let uu____9024 =
                                                               FStar_All.pipe_right
                                                                 lb.FStar_Syntax_Syntax.lbname
                                                                 FStar_Util.right
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____9024
                                                               (fun fv  ->
                                                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                              in
                                                           [uu____9023]  in
                                                         ((false, [lb]),
                                                           uu____9020)
                                                          in
                                                       FStar_Syntax_Syntax.Sig_let
                                                         uu____9013
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.sigel
                                                         = uu____9012;
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
                                                   (let uu____9038 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        (FStar_Options.Other
                                                           "LogTypes")
                                                       in
                                                    if uu____9038
                                                    then
                                                      let uu____9042 =
                                                        FStar_Syntax_Print.sigelt_to_string
                                                          impl
                                                         in
                                                      FStar_Util.print1
                                                        "Implementation of a projector %s\n"
                                                        uu____9042
                                                    else ());
                                                   if no_decl
                                                   then [impl]
                                                   else [decl; impl])))))
                             in
                          FStar_All.pipe_right uu____8534 FStar_List.flatten
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
              (constr_lid,uvs,t,typ_lid,n_typars,uu____9096) when
              let uu____9103 =
                FStar_Ident.lid_equals constr_lid
                  FStar_Parser_Const.lexcons_lid
                 in
              Prims.op_Negation uu____9103 ->
              let uu____9105 = FStar_Syntax_Subst.univ_var_opening uvs  in
              (match uu____9105 with
               | (univ_opening,uvs1) ->
                   let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                   let uu____9127 = FStar_Syntax_Util.arrow_formals t1  in
                   (match uu____9127 with
                    | (formals,uu____9145) ->
                        let uu____9166 =
                          let tps_opt =
                            FStar_Util.find_map tcs
                              (fun se1  ->
                                 let uu____9201 =
                                   let uu____9203 =
                                     let uu____9204 =
                                       FStar_Syntax_Util.lid_of_sigelt se1
                                        in
                                     FStar_Util.must uu____9204  in
                                   FStar_Ident.lid_equals typ_lid uu____9203
                                    in
                                 if uu____9201
                                 then
                                   match se1.FStar_Syntax_Syntax.sigel with
                                   | FStar_Syntax_Syntax.Sig_inductive_typ
                                       (uu____9226,uvs',tps,typ0,uu____9230,constrs)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         (tps, typ0,
                                           ((FStar_List.length constrs) >
                                              Prims.int_one))
                                   | uu____9250 -> failwith "Impossible"
                                 else FStar_Pervasives_Native.None)
                             in
                          match tps_opt with
                          | FStar_Pervasives_Native.Some x -> x
                          | FStar_Pervasives_Native.None  ->
                              let uu____9299 =
                                FStar_Ident.lid_equals typ_lid
                                  FStar_Parser_Const.exn_lid
                                 in
                              if uu____9299
                              then ([], FStar_Syntax_Util.ktype0, true)
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                    "Unexpected data constructor")
                                  se.FStar_Syntax_Syntax.sigrng
                           in
                        (match uu____9166 with
                         | (inductive_tps,typ0,should_refine) ->
                             let inductive_tps1 =
                               FStar_Syntax_Subst.subst_binders univ_opening
                                 inductive_tps
                                in
                             let typ01 =
                               FStar_Syntax_Subst.subst univ_opening typ0  in
                             let uu____9337 =
                               FStar_Syntax_Util.arrow_formals typ01  in
                             (match uu____9337 with
                              | (indices,uu____9355) ->
                                  let refine_domain =
                                    let uu____9378 =
                                      FStar_All.pipe_right
                                        se.FStar_Syntax_Syntax.sigquals
                                        (FStar_Util.for_some
                                           (fun uu___7_9385  ->
                                              match uu___7_9385 with
                                              | FStar_Syntax_Syntax.RecordConstructor
                                                  uu____9387 -> true
                                              | uu____9397 -> false))
                                       in
                                    if uu____9378
                                    then false
                                    else should_refine  in
                                  let fv_qual =
                                    let filter_records uu___8_9412 =
                                      match uu___8_9412 with
                                      | FStar_Syntax_Syntax.RecordConstructor
                                          (uu____9415,fns) ->
                                          FStar_Pervasives_Native.Some
                                            (FStar_Syntax_Syntax.Record_ctor
                                               (constr_lid, fns))
                                      | uu____9427 ->
                                          FStar_Pervasives_Native.None
                                       in
                                    let uu____9428 =
                                      FStar_Util.find_map
                                        se.FStar_Syntax_Syntax.sigquals
                                        filter_records
                                       in
                                    match uu____9428 with
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
                                    let uu____9441 =
                                      FStar_Util.first_N n_typars formals  in
                                    match uu____9441 with
                                    | (imp_tps,fields) ->
                                        let rename =
                                          FStar_List.map2
                                            (fun uu____9524  ->
                                               fun uu____9525  ->
                                                 match (uu____9524,
                                                         uu____9525)
                                                 with
                                                 | ((x,uu____9551),(x',uu____9553))
                                                     ->
                                                     let uu____9574 =
                                                       let uu____9581 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x'
                                                          in
                                                       (x, uu____9581)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____9574) imp_tps
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
          | uu____9588 -> []
  