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
                             let uu____808 =
                               let uu____809 = FStar_Syntax_Subst.compress t2
                                  in
                               uu____809.FStar_Syntax_Syntax.n  in
                             match uu____808 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,res) ->
                                 let uu____840 = FStar_Util.first_N ntps bs
                                    in
                                 (match uu____840 with
                                  | (uu____873,bs') ->
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
                                                fun uu____944  ->
                                                  match uu____944 with
                                                  | (x,uu____953) ->
                                                      FStar_Syntax_Syntax.DB
                                                        ((ntps -
                                                            (Prims.int_one +
                                                               i)), x)))
                                         in
                                      let uu____960 =
                                        let uu____973 =
                                          FStar_Syntax_Subst.subst subst1 t3
                                           in
                                        FStar_Syntax_Util.arrow_formals_comp
                                          uu____973
                                         in
                                      (match uu____960 with
                                       | (bs1,c1) ->
                                           let uu____998 =
                                             (FStar_Options.ml_ish ()) ||
                                               (FStar_Syntax_Util.is_total_comp
                                                  c1)
                                              in
                                           if uu____998
                                           then
                                             (bs1,
                                               (FStar_Syntax_Util.comp_result
                                                  c1))
                                           else
                                             (let uu____1011 =
                                                FStar_Ident.range_of_lid
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c1)
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                  "Constructors cannot have effects")
                                                uu____1011)))
                             | uu____1020 -> ([], t2)  in
                           (match uu____800 with
                            | (arguments,result) ->
                                ((let uu____1040 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____1040
                                  then
                                    let uu____1043 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____1045 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____1048 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1043 uu____1045 uu____1048
                                  else ());
                                 (let uu____1053 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____1053 with
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
                                      let uu____1071 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____1071 with
                                       | (result1,res_lcomp) ->
                                           let uu____1082 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____1082 with
                                            | (head1,args) ->
                                                let p_args =
                                                  let uu____1140 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1140
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____1222  ->
                                                      fun uu____1223  ->
                                                        match (uu____1222,
                                                                uu____1223)
                                                        with
                                                        | ((bv,uu____1253),
                                                           (t2,uu____1255))
                                                            ->
                                                            let uu____1282 =
                                                              let uu____1283
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____1283.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____1282
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1287 ->
                                                                 let uu____1288
                                                                   =
                                                                   let uu____1294
                                                                    =
                                                                    let uu____1296
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____1298
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1296
                                                                    uu____1298
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1294)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____1288
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1303 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_TypeChecker_Common.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1303
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____1305 =
                                                     let uu____1306 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____1306.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1305 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1309 -> ()
                                                   | uu____1310 ->
                                                       let uu____1311 =
                                                         let uu____1317 =
                                                           let uu____1319 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____1321 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1319
                                                             uu____1321
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1317)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1311
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1326 =
                                                       let uu____1327 =
                                                         FStar_Syntax_Subst.compress
                                                           head1
                                                          in
                                                       uu____1327.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____1326 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1331;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1332;_},tuvs)
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
                                                                    let uu____1346
                                                                    =
                                                                    let uu____1347
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1348
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
                                                                    uu____1347
                                                                    uu____1348
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1346)
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
                                                     | uu____1354 ->
                                                         let uu____1355 =
                                                           let uu____1361 =
                                                             let uu____1363 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____1365 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head1
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1363
                                                               uu____1365
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1361)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____1355
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____1383  ->
                                                            fun u_x  ->
                                                              match uu____1383
                                                              with
                                                              | (x,uu____1392)
                                                                  ->
                                                                  let uu____1397
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1397)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____1401 =
                                                       let uu____1410 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1450
                                                                  ->
                                                                 match uu____1450
                                                                 with
                                                                 | (x,uu____1464)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____1410
                                                         arguments1
                                                        in
                                                     let uu____1478 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1401 uu____1478
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___187_1483 = se
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
                                                         (uu___187_1483.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___187_1483.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___187_1483.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___187_1483.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___187_1483.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1487 -> failwith "impossible"
  
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
               (fun uu____1578  ->
                  match uu____1578 with
                  | (se,uu____1584) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1585,uu____1586,tps,k,uu____1589,uu____1590)
                           ->
                           let uu____1599 =
                             let uu____1600 = FStar_Syntax_Syntax.mk_Total k
                                in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1600
                              in
                           FStar_Syntax_Syntax.null_binder uu____1599
                       | uu____1605 -> failwith "Impossible")))
           in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1634,uu____1635,t,uu____1637,uu____1638,uu____1639)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1646 -> failwith "Impossible"))
           in
        let t =
          let uu____1651 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1651
           in
        (let uu____1661 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses")
            in
         if uu____1661
         then
           let uu____1666 = FStar_TypeChecker_Normalize.term_to_string env t
              in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1666
         else ());
        (let uu____1671 = FStar_TypeChecker_Util.generalize_universes env t
            in
         match uu____1671 with
         | (uvs,t1) ->
             ((let uu____1691 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses")
                  in
               if uu____1691
               then
                 let uu____1696 =
                   let uu____1698 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                      in
                   FStar_All.pipe_right uu____1698 (FStar_String.concat ", ")
                    in
                 let uu____1715 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1696 uu____1715
               else ());
              (let uu____1720 = FStar_Syntax_Subst.open_univ_vars uvs t1  in
               match uu____1720 with
               | (uvs1,t2) ->
                   let uu____1735 = FStar_Syntax_Util.arrow_formals t2  in
                   (match uu____1735 with
                    | (args,uu____1759) ->
                        let uu____1780 =
                          FStar_Util.first_N (FStar_List.length binders) args
                           in
                        (match uu____1780 with
                         | (tc_types,data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1885  ->
                                    fun uu____1886  ->
                                      match (uu____1885, uu____1886) with
                                      | ((x,uu____1908),(se,uu____1910)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc,uu____1926,tps,uu____1928,mutuals,datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let uu____1940 =
                                                 let uu____1945 =
                                                   let uu____1946 =
                                                     FStar_Syntax_Subst.compress
                                                       ty
                                                      in
                                                   uu____1946.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____1945 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1,c) ->
                                                     let uu____1975 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1
                                                        in
                                                     (match uu____1975 with
                                                      | (tps1,rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____2053 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  FStar_Pervasives_Native.None
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                             in
                                                          (tps1, t3))
                                                 | uu____2072 -> ([], ty)  in
                                               (match uu____1940 with
                                                | (tps1,t3) ->
                                                    let uu___264_2081 = se
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
                                                        (uu___264_2081.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___264_2081.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___264_2081.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___264_2081.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___264_2081.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____2086 ->
                                               failwith "Impossible"))
                                 tc_types tcs
                                in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____2093 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun _2097  ->
                                             FStar_Syntax_Syntax.U_name _2097))
                                      in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_2117  ->
                                             match uu___0_2117 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc,uu____2123,uu____2124,uu____2125,uu____2126,uu____2127);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____2128;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____2129;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____2130;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____2131;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____2132;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2147 ->
                                                 failwith "Impossible"))
                                      in
                                   FStar_List.map2
                                     (fun uu____2171  ->
                                        fun d  ->
                                          match uu____2171 with
                                          | (t3,uu____2180) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l,uu____2186,uu____2187,tc,ntps,mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2198 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2198
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1)
                                                      in
                                                   let uu___301_2199 = d  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___301_2199.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___301_2199.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___301_2199.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___301_2199.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___301_2199.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu____2203 ->
                                                   failwith "Impossible"))
                                     data_types datas
                                in
                             (tcs1, datas1))))))
  
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env  ->
    fun msg  ->
      let uu____2227 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2227
      then
        let uu____2232 =
          let uu____2234 =
            let uu____2236 = msg ()  in Prims.op_Hat uu____2236 "\n"  in
          Prims.op_Hat "Positivity::" uu____2234  in
        FStar_Util.print_string uu____2232
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2255 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2255
  
let (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes))
  =
  fun t  ->
    let uu____2272 =
      let uu____2273 = FStar_Syntax_Subst.compress t  in
      uu____2273.FStar_Syntax_Syntax.n  in
    match uu____2272 with
    | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        (match t1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv -> (fv, us)
         | uu____2292 ->
             failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | uu____2298 -> failwith "Node is not an fvar or a Tm_uinst"
  
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
          let uu____2335 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2384  ->
               match uu____2384 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2428 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2428  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2335
  
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
            (fun uu____2635  ->
               let uu____2636 = FStar_Syntax_Print.term_to_string btype  in
               Prims.op_Hat "Checking strict positivity in type: " uu____2636);
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
             (fun uu____2643  ->
                let uu____2644 = FStar_Syntax_Print.term_to_string btype1  in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu____2644);
           (let uu____2649 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2649) ||
             ((debug_log env
                 (fun uu____2662  ->
                    "ty does occur in this type, pressing ahead");
               (let uu____2664 =
                  let uu____2665 = FStar_Syntax_Subst.compress btype1  in
                  uu____2665.FStar_Syntax_Syntax.n  in
                match uu____2664 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let uu____2695 = try_get_fv t  in
                    (match uu____2695 with
                     | (fv,us) ->
                         let uu____2703 =
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             ty_lid
                            in
                         if uu____2703
                         then
                           (debug_log env
                              (fun uu____2709  ->
                                 "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                            FStar_List.for_all
                              (fun uu____2721  ->
                                 match uu____2721 with
                                 | (t1,uu____2730) ->
                                     let uu____2735 = ty_occurs_in ty_lid t1
                                        in
                                     Prims.op_Negation uu____2735) args)
                         else
                           (debug_log env
                              (fun uu____2741  ->
                                 "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                            ty_nested_positive_in_inductive ty_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env
                       (fun uu____2767  ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp1 =
                        let c1 =
                          let uu____2774 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2774
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2778 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2778
                             (FStar_List.existsb
                                (fun q  ->
                                   q = FStar_Syntax_Syntax.TotalEffect)))
                         in
                      if Prims.op_Negation check_comp1
                      then
                        (debug_log env
                           (fun uu____2790  ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu____2797  ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu____2809  ->
                               match uu____2809 with
                               | (b,uu____2818) ->
                                   let uu____2823 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2823) sbs)
                           &&
                           ((let uu____2829 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2829 with
                             | (uu____2835,return_type) ->
                                 let uu____2837 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2837)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2838 ->
                    (debug_log env
                       (fun uu____2841  ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2844 ->
                    (debug_log env
                       (fun uu____2847  ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2851) ->
                    (debug_log env
                       (fun uu____2858  ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2861) ->
                    (debug_log env
                       (fun uu____2868  ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2870,branches) ->
                    (debug_log env
                       (fun uu____2910  ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu____2931  ->
                          match uu____2931 with
                          | (p,uu____2944,t) ->
                              let bs =
                                let uu____2963 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____2963
                                 in
                              let uu____2972 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____2972 with
                               | (bs1,t1) ->
                                   let uu____2980 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____2980)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____2982,uu____2983)
                    ->
                    (debug_log env
                       (fun uu____3026  ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____3028 ->
                    (debug_log env
                       (fun uu____3032  ->
                          let uu____3033 =
                            let uu____3035 =
                              FStar_Syntax_Print.tag_of_term btype1  in
                            let uu____3037 =
                              let uu____3039 =
                                FStar_Syntax_Print.term_to_string btype1  in
                              Prims.op_Hat " and term: " uu____3039  in
                            Prims.op_Hat uu____3035 uu____3037  in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu____3033);
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
                (fun uu____3054  ->
                   let uu____3055 =
                     let uu____3057 =
                       let uu____3059 =
                         FStar_Syntax_Print.args_to_string args  in
                       Prims.op_Hat " applied to arguments: " uu____3059  in
                     Prims.op_Hat ilid.FStar_Ident.str uu____3057  in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive "
                     uu____3055);
              (let uu____3063 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3063 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3082 =
                       let uu____3084 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3084
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____3082
                      then
                        (debug_log env
                           (fun uu____3090  ->
                              let uu____3091 = FStar_Ident.string_of_lid ilid
                                 in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu____3091);
                         true)
                      else
                        (debug_log env
                           (fun uu____3099  ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu____3104 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3104
                      then
                        (debug_log env
                           (fun uu____3110  ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu____3117 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3117  in
                         debug_log env
                           (fun uu____3125  ->
                              let uu____3126 =
                                let uu____3128 =
                                  FStar_Util.string_of_int num_ibs  in
                                Prims.op_Hat uu____3128
                                  ", also adding to the memo table"
                                 in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu____3126);
                         (let uu____3133 =
                            let uu____3134 = FStar_ST.op_Bang unfolded  in
                            let uu____3160 =
                              let uu____3167 =
                                let uu____3172 =
                                  let uu____3173 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3173  in
                                (ilid, uu____3172)  in
                              [uu____3167]  in
                            FStar_List.append uu____3134 uu____3160  in
                          FStar_ST.op_Colon_Equals unfolded uu____3133);
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
                    (fun uu____3271  ->
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         (Prims.op_Hat dlid.FStar_Ident.str
                            (Prims.op_Hat " of the inductive "
                               ilid.FStar_Ident.str)));
                  (let uu____3274 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3274 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3297 ->
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
                           (fun uu____3303  ->
                              let uu____3304 =
                                FStar_Syntax_Print.term_to_string dt1  in
                              Prims.op_Hat
                                "Checking nested positivity in the data constructor type: "
                                uu____3304);
                         (let uu____3307 =
                            let uu____3308 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3308.FStar_Syntax_Syntax.n  in
                          match uu____3307 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 (fun uu____3336  ->
                                    "Checked nested positivity in Tm_arrow data constructor type");
                               (let uu____3338 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3338 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3402 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3402 dbs1
                                       in
                                    let c1 =
                                      let uu____3406 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3406 c
                                       in
                                    let uu____3409 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3409 with
                                     | (args1,uu____3444) ->
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
                                           let uu____3536 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3)
                                               subst1
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3536 c1
                                            in
                                         (debug_log env
                                            (fun uu____3548  ->
                                               let uu____3549 =
                                                 let uu____3551 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     "; " dbs3
                                                    in
                                                 let uu____3554 =
                                                   let uu____3556 =
                                                     FStar_Syntax_Print.comp_to_string
                                                       c2
                                                      in
                                                   Prims.op_Hat ", and c: "
                                                     uu____3556
                                                    in
                                                 Prims.op_Hat uu____3551
                                                   uu____3554
                                                  in
                                               Prims.op_Hat
                                                 "Checking nested positivity in the unfolded data constructor binders as: "
                                                 uu____3549);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3570 ->
                              (debug_log env
                                 (fun uu____3573  ->
                                    "Checking nested positivity in the data constructor type that is not an arrow");
                               (let uu____3575 =
                                  let uu____3576 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3576.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3575
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
                     (fun uu____3615  ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu____3617 = try_get_fv t1  in
                    match uu____3617 with
                    | (fv,uu____3624) ->
                        let uu____3625 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3625
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  (debug_log env
                     (fun uu____3659  ->
                        let uu____3660 =
                          FStar_Syntax_Print.binders_to_string "; " sbs  in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu____3660);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3665 =
                      FStar_List.fold_left
                        (fun uu____3686  ->
                           fun b  ->
                             match uu____3686 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3717 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3721 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3717, uu____3721))) (true, env)
                        sbs1
                       in
                    match uu____3665 with | (b,uu____3739) -> b))
              | uu____3742 ->
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
              let uu____3778 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3778 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3801 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu____3806  ->
                        let uu____3807 = FStar_Syntax_Print.term_to_string dt
                           in
                        Prims.op_Hat "Checking data constructor type: "
                          uu____3807);
                   (let uu____3810 =
                      let uu____3811 = FStar_Syntax_Subst.compress dt  in
                      uu____3811.FStar_Syntax_Syntax.n  in
                    match uu____3810 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3815 ->
                        (debug_log env
                           (fun uu____3818  ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3822) ->
                        let dbs1 =
                          let uu____3852 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3852  in
                        let dbs2 =
                          let uu____3902 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3902 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        (debug_log env
                           (fun uu____3909  ->
                              let uu____3910 =
                                let uu____3912 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3)
                                   in
                                Prims.op_Hat uu____3912 " binders"  in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu____3910);
                         (let uu____3922 =
                            FStar_List.fold_left
                              (fun uu____3943  ->
                                 fun b  ->
                                   match uu____3943 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____3974 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____3978 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____3974, uu____3978)))
                              (true, env) dbs3
                             in
                          match uu____3922 with | (b,uu____3996) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____3999,uu____4000) ->
                        (debug_log env
                           (fun uu____4027  ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs1) ->
                        (debug_log env
                           (fun uu____4038  ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____4040 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____4063 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4079,uu____4080,uu____4081) -> (lid, us, bs)
        | uu____4090 -> failwith "Impossible!"  in
      match uu____4063 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4102 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4102 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4126 =
                 let uu____4129 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4129  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4143 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4143
                      unfolded_inductives env2) uu____4126)
  
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
        (uu____4178,uu____4179,t,uu____4181,uu____4182,uu____4183) -> t
    | uu____4190 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4207 =
         let uu____4209 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4209 haseq_suffix  in
       uu____4207 = Prims.int_zero)
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4219 =
      let uu____4222 =
        let uu____4225 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4225]  in
      FStar_List.append lid.FStar_Ident.ns uu____4222  in
    FStar_Ident.lid_of_ids uu____4219
  
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
          let uu____4271 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4285,bs,t,uu____4288,uu____4289) -> (lid, bs, t)
            | uu____4298 -> failwith "Impossible!"  in
          match uu____4271 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4321 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4321 t  in
              let uu____4330 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4330 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4348 =
                       let uu____4349 = FStar_Syntax_Subst.compress t2  in
                       uu____4349.FStar_Syntax_Syntax.n  in
                     match uu____4348 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4353) -> ibs
                     | uu____4374 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4383 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4384 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4383 uu____4384
                      in
                   let ind1 =
                     let uu____4390 =
                       let uu____4395 =
                         FStar_List.map
                           (fun uu____4412  ->
                              match uu____4412 with
                              | (bv,aq) ->
                                  let uu____4431 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4431, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4395  in
                     uu____4390 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4437 =
                       let uu____4442 =
                         FStar_List.map
                           (fun uu____4459  ->
                              match uu____4459 with
                              | (bv,aq) ->
                                  let uu____4478 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4478, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4442  in
                     uu____4437 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4484 =
                       let uu____4489 =
                         let uu____4490 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4490]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4489
                        in
                     uu____4484 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4539 =
                            let uu____4540 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4540  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4539) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4553 =
                              let uu____4556 =
                                let uu____4561 =
                                  let uu____4562 =
                                    let uu____4571 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4571  in
                                  [uu____4562]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4561
                                 in
                              uu____4556 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4553)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___667_4594 = fml  in
                     let uu____4595 =
                       let uu____4596 =
                         let uu____4603 =
                           let uu____4604 =
                             let uu____4625 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____4630 =
                               let uu____4643 =
                                 let uu____4654 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____4654]  in
                               [uu____4643]  in
                             (uu____4625, uu____4630)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4604  in
                         (fml, uu____4603)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4596  in
                     {
                       FStar_Syntax_Syntax.n = uu____4595;
                       FStar_Syntax_Syntax.pos =
                         (uu___667_4594.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___667_4594.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4723 =
                              let uu____4728 =
                                let uu____4729 =
                                  let uu____4738 =
                                    let uu____4739 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4739 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4738  in
                                [uu____4729]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4728
                               in
                            uu____4723 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4792 =
                              let uu____4797 =
                                let uu____4798 =
                                  let uu____4807 =
                                    let uu____4808 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4808 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4807  in
                                [uu____4798]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4797
                               in
                            uu____4792 FStar_Pervasives_Native.None
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
          let uu____4883 =
            let uu____4884 = FStar_Syntax_Subst.compress dt1  in
            uu____4884.FStar_Syntax_Syntax.n  in
          match uu____4883 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4888) ->
              let dbs1 =
                let uu____4918 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____4918  in
              let dbs2 =
                let uu____4968 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____4968 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____4983 =
                           let uu____4988 =
                             let uu____4989 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____4989]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____4988
                            in
                         uu____4983 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____5020 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____5020 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____5028 =
                       let uu____5033 =
                         let uu____5034 =
                           let uu____5043 =
                             let uu____5044 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____5044
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____5043  in
                         [uu____5034]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____5033
                        in
                     uu____5028 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5091 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5182,uu____5183,uu____5184,uu____5185,uu____5186)
                  -> lid
              | uu____5195 -> failwith "Impossible!"  in
            let uu____5197 = acc  in
            match uu____5197 with
            | (uu____5234,en,uu____5236,uu____5237) ->
                let uu____5258 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5258 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5295 = acc  in
                     (match uu____5295 with
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
                                     (uu____5370,uu____5371,uu____5372,t_lid,uu____5374,uu____5375)
                                     -> t_lid = lid
                                 | uu____5382 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5397 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5397)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5400 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5403 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5400, uu____5403)))
  
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
          let uu____5461 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5471,us,uu____5473,t,uu____5475,uu____5476) -> 
                (us, t)
            | uu____5485 -> failwith "Impossible!"  in
          match uu____5461 with
          | (us,t) ->
              let uu____5495 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5495 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5521 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5521 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5599 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5599 with
                           | (uu____5614,t1) ->
                               let uu____5636 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5636
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5641 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5641 with
                          | (phi1,uu____5649) ->
                              ((let uu____5651 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5651
                                then
                                  let uu____5654 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5654
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5672  ->
                                         match uu____5672 with
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
                let uu____5744 =
                  let uu____5745 = FStar_Syntax_Subst.compress t  in
                  uu____5745.FStar_Syntax_Syntax.n  in
                match uu____5744 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5753) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5790 = is_mutual t'  in
                    if uu____5790
                    then true
                    else
                      (let uu____5797 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5797)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5817) -> is_mutual t'
                | uu____5822 -> false
              
              and exists_mutual uu___1_5824 =
                match uu___1_5824 with
                | [] -> false
                | hd1::tl1 -> (is_mutual hd1) || (exists_mutual tl1)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5845 =
                let uu____5846 = FStar_Syntax_Subst.compress dt1  in
                uu____5846.FStar_Syntax_Syntax.n  in
              match uu____5845 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5852) ->
                  let dbs1 =
                    let uu____5882 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5882  in
                  let dbs2 =
                    let uu____5932 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5932 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____5952 =
                               let uu____5957 =
                                 let uu____5958 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____5958]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____5957
                                in
                             uu____5952 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____5988 = is_mutual sort  in
                             if uu____5988
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
                           let uu____6001 =
                             let uu____6006 =
                               let uu____6007 =
                                 let uu____6016 =
                                   let uu____6017 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____6017 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____6016  in
                               [uu____6007]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____6006
                              in
                           uu____6001 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____6064 -> acc
  
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
              let uu____6114 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6136,bs,t,uu____6139,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6151 -> failwith "Impossible!"  in
              match uu____6114 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6175 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6175 t  in
                  let uu____6184 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6184 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6194 =
                           let uu____6195 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6195.FStar_Syntax_Syntax.n  in
                         match uu____6194 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6199) ->
                             ibs
                         | uu____6220 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6229 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6230 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6229
                           uu____6230
                          in
                       let ind1 =
                         let uu____6236 =
                           let uu____6241 =
                             FStar_List.map
                               (fun uu____6258  ->
                                  match uu____6258 with
                                  | (bv,aq) ->
                                      let uu____6277 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6277, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6241  in
                         uu____6236 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6283 =
                           let uu____6288 =
                             FStar_List.map
                               (fun uu____6305  ->
                                  match uu____6305 with
                                  | (bv,aq) ->
                                      let uu____6324 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6324, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6288  in
                         uu____6283 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6330 =
                           let uu____6335 =
                             let uu____6336 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6336]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6335
                            in
                         uu____6330 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6373,uu____6374,uu____6375,t_lid,uu____6377,uu____6378)
                                  -> t_lid = lid
                              | uu____6385 -> failwith "Impossible")
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
                         let uu___904_6397 = fml  in
                         let uu____6398 =
                           let uu____6399 =
                             let uu____6406 =
                               let uu____6407 =
                                 let uu____6428 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____6433 =
                                   let uu____6446 =
                                     let uu____6457 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____6457]  in
                                   [uu____6446]  in
                                 (uu____6428, uu____6433)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6407
                                in
                             (fml, uu____6406)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6399  in
                         {
                           FStar_Syntax_Syntax.n = uu____6398;
                           FStar_Syntax_Syntax.pos =
                             (uu___904_6397.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___904_6397.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6526 =
                                  let uu____6531 =
                                    let uu____6532 =
                                      let uu____6541 =
                                        let uu____6542 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6542
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6541
                                       in
                                    [uu____6532]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6531
                                   in
                                uu____6526 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6595 =
                                  let uu____6600 =
                                    let uu____6601 =
                                      let uu____6610 =
                                        let uu____6611 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6611
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6610
                                       in
                                    [uu____6601]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6600
                                   in
                                uu____6595 FStar_Pervasives_Native.None
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
                     (lid,uu____6703,uu____6704,uu____6705,uu____6706,uu____6707)
                     -> lid
                 | uu____6716 -> failwith "Impossible!") tcs
             in
          let uu____6718 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6730,uu____6731,uu____6732,uu____6733) ->
                (lid, us)
            | uu____6742 -> failwith "Impossible!"  in
          match uu____6718 with
          | (lid,us) ->
              let uu____6752 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6752 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6779 =
                       let uu____6780 =
                         let uu____6787 = get_haseq_axiom_lid lid  in
                         (uu____6787, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6780  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6779;
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
          let uu____6841 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6867  ->
                    match uu___2_6867 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6869;
                        FStar_Syntax_Syntax.sigrng = uu____6870;
                        FStar_Syntax_Syntax.sigquals = uu____6871;
                        FStar_Syntax_Syntax.sigmeta = uu____6872;
                        FStar_Syntax_Syntax.sigattrs = uu____6873;
                        FStar_Syntax_Syntax.sigopts = uu____6874;_} -> true
                    | uu____6898 -> false))
             in
          match uu____6841 with
          | (tys,datas) ->
              ((let uu____6921 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6933  ->
                          match uu___3_6933 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6935;
                              FStar_Syntax_Syntax.sigrng = uu____6936;
                              FStar_Syntax_Syntax.sigquals = uu____6937;
                              FStar_Syntax_Syntax.sigmeta = uu____6938;
                              FStar_Syntax_Syntax.sigattrs = uu____6939;
                              FStar_Syntax_Syntax.sigopts = uu____6940;_} ->
                              false
                          | uu____6963 -> true))
                   in
                if uu____6921
                then
                  let uu____6966 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____6966
                else ());
               (let univs1 =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____6981 =
                       let uu____6982 = FStar_List.hd tys  in
                       uu____6982.FStar_Syntax_Syntax.sigel  in
                     match uu____6981 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____6985,uvs,uu____6987,uu____6988,uu____6989,uu____6990)
                         -> uvs
                     | uu____6999 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____7004 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____7043  ->
                         match uu____7043 with
                         | (env1,all_tcs,g) ->
                             let uu____7083 = tc_tycon env1 tc  in
                             (match uu____7083 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____7110 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____7110
                                    then
                                      let uu____7113 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____7113
                                    else ());
                                   (let uu____7118 =
                                      let uu____7119 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____7119
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____7118))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard)
                   in
                match uu____7004 with
                | (env1,tcs,g) ->
                    let uu____7165 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____7187  ->
                             match uu____7187 with
                             | (datas1,g1) ->
                                 let uu____7206 =
                                   let uu____7211 = tc_data env1 tcs  in
                                   uu____7211 se  in
                                 (match uu____7206 with
                                  | (data,g') ->
                                      let uu____7228 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____7228))) datas
                        ([], g)
                       in
                    (match uu____7165 with
                     | (datas1,g1) ->
                         let uu____7249 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs
                              in
                           let g2 =
                             let uu___1015_7266 = g1  in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___1015_7266.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___1015_7266.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___1015_7266.FStar_TypeChecker_Common.implicits)
                             }  in
                           (let uu____7276 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses")
                               in
                            if uu____7276
                            then
                              let uu____7281 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2
                                 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____7281
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs1) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____7300 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs
                                 in
                              (uu____7300, datas1))
                            in
                         (match uu____7249 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____7332 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                let uu____7333 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses
                                   in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____7332;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____7333;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                }  in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs2,binders,typ,uu____7359,uu____7360)
                                           ->
                                           let fail1 expected inferred =
                                             let uu____7380 =
                                               let uu____7386 =
                                                 let uu____7388 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected
                                                    in
                                                 let uu____7390 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred
                                                    in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____7388 uu____7390
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____7386)
                                                in
                                             FStar_Errors.raise_error
                                               uu____7380
                                               se.FStar_Syntax_Syntax.sigrng
                                              in
                                           let uu____7394 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l
                                              in
                                           (match uu____7394 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ1,uu____7410) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____7441 ->
                                                        let uu____7442 =
                                                          let uu____7449 =
                                                            let uu____7450 =
                                                              let uu____7465
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ
                                                                 in
                                                              (binders,
                                                                uu____7465)
                                                               in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____7450
                                                             in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____7449
                                                           in
                                                        uu____7442
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
                                                  let uu____7487 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ
                                                     in
                                                  (match uu____7487 with
                                                   | (uu____7492,inferred) ->
                                                       let uu____7494 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ1
                                                          in
                                                       (match uu____7494 with
                                                        | (uu____7499,expected)
                                                            ->
                                                            let uu____7501 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected
                                                               in
                                                            if uu____7501
                                                            then ()
                                                            else
                                                              fail1
                                                                expected_typ1
                                                                inferred_typ))
                                                else
                                                  fail1 expected_typ1
                                                    inferred_typ)
                                       | uu____7508 -> ()));
                               (sig_bndle, tcs1, datas2))))))
  
let (early_prims_inductives : Prims.string Prims.list) =
  ["c_False"; "c_True"; "equals"; "h_equals"; "c_and"; "c_or"] 
let (mk_discriminator_and_indexed_projectors :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
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
    fun attrs  ->
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
                              let uu____7635 =
                                let uu____7642 =
                                  let uu____7643 =
                                    let uu____7650 =
                                      let uu____7653 =
                                        FStar_Syntax_Syntax.lid_as_fv tc
                                          FStar_Syntax_Syntax.delta_constant
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.fv_to_tm uu____7653
                                       in
                                    (uu____7650, inst_univs)  in
                                  FStar_Syntax_Syntax.Tm_uinst uu____7643  in
                                FStar_Syntax_Syntax.mk uu____7642  in
                              uu____7635 FStar_Pervasives_Native.None p  in
                            let args =
                              FStar_All.pipe_right
                                (FStar_List.append tps indices)
                                (FStar_List.map
                                   (fun uu____7687  ->
                                      match uu____7687 with
                                      | (x,imp) ->
                                          let uu____7706 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7706, imp)))
                               in
                            FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                              FStar_Pervasives_Native.None p
                             in
                          let unrefined_arg_binder =
                            let uu____7710 = projectee arg_typ  in
                            FStar_Syntax_Syntax.mk_binder uu____7710  in
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
                                   let uu____7733 =
                                     FStar_Ident.set_lid_range disc_name p
                                      in
                                   FStar_Syntax_Syntax.fvar uu____7733
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                     FStar_Pervasives_Native.None
                                    in
                                 let uu____7735 =
                                   let uu____7738 =
                                     let uu____7741 =
                                       let uu____7746 =
                                         FStar_Syntax_Syntax.mk_Tm_uinst
                                           disc_fvar inst_univs
                                          in
                                       let uu____7747 =
                                         let uu____7748 =
                                           let uu____7757 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             uu____7757
                                            in
                                         [uu____7748]  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____7746 uu____7747
                                        in
                                     uu____7741 FStar_Pervasives_Native.None
                                       p
                                      in
                                   FStar_Syntax_Util.b2t uu____7738  in
                                 FStar_Syntax_Util.refine x uu____7735  in
                               let uu____7782 =
                                 let uu___1090_7783 = projectee arg_typ  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1090_7783.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1090_7783.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = sort
                                 }  in
                               FStar_Syntax_Syntax.mk_binder uu____7782)
                             in
                          let ntps = FStar_List.length tps  in
                          let all_params =
                            let uu____7800 =
                              FStar_List.map
                                (fun uu____7824  ->
                                   match uu____7824 with
                                   | (x,uu____7838) ->
                                       (x,
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.imp_tag)))
                                tps
                               in
                            FStar_List.append uu____7800 fields  in
                          let imp_binders =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7897  ->
                                    match uu____7897 with
                                    | (x,uu____7911) ->
                                        (x,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag))))
                             in
                          let early_prims_inductive =
                            (let uu____7922 =
                               FStar_TypeChecker_Env.current_module env  in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu____7922)
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
                                   (let uu____7943 =
                                      let uu____7945 =
                                        FStar_TypeChecker_Env.current_module
                                          env
                                         in
                                      uu____7945.FStar_Ident.str  in
                                    FStar_Options.dont_gen_projectors
                                      uu____7943)
                                  in
                               let quals =
                                 let uu____7949 =
                                   FStar_List.filter
                                     (fun uu___4_7953  ->
                                        match uu___4_7953 with
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            Prims.op_Negation only_decl
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                             -> true
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____7958 -> false) iquals
                                    in
                                 FStar_List.append
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu____7949
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
                                 let uu____8003 =
                                   FStar_Syntax_Util.arrow binders bool_typ
                                    in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close_univ_vars uvs)
                                   uu____8003
                                  in
                               let decl =
                                 let uu____8007 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        (discriminator_name, uvs, t));
                                   FStar_Syntax_Syntax.sigrng = uu____8007;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               (let uu____8009 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes")
                                   in
                                if uu____8009
                                then
                                  let uu____8013 =
                                    FStar_Syntax_Print.sigelt_to_string decl
                                     in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu____8013
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
                                                 fun uu____8074  ->
                                                   match uu____8074 with
                                                   | (x,imp) ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_implicit
                                                           imp
                                                          in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu____8099 =
                                                           let uu____8102 =
                                                             let uu____8103 =
                                                               let uu____8110
                                                                 =
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               (uu____8110,
                                                                 FStar_Syntax_Syntax.tun)
                                                                in
                                                             FStar_Syntax_Syntax.Pat_dot_term
                                                               uu____8103
                                                              in
                                                           pos uu____8102  in
                                                         (uu____8099, b)
                                                       else
                                                         (let uu____8118 =
                                                            let uu____8121 =
                                                              let uu____8122
                                                                =
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun
                                                                 in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu____8122
                                                               in
                                                            pos uu____8121
                                                             in
                                                          (uu____8118, b))))
                                          in
                                       let pat_true =
                                         let uu____8141 =
                                           let uu____8144 =
                                             let uu____8145 =
                                               let uu____8159 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   (FStar_Pervasives_Native.Some
                                                      fvq)
                                                  in
                                               (uu____8159, arg_pats)  in
                                             FStar_Syntax_Syntax.Pat_cons
                                               uu____8145
                                              in
                                           pos uu____8144  in
                                         (uu____8141,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_true_bool)
                                          in
                                       let pat_false =
                                         let uu____8194 =
                                           let uu____8197 =
                                             let uu____8198 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Syntax.tun
                                                in
                                             FStar_Syntax_Syntax.Pat_wild
                                               uu____8198
                                              in
                                           pos uu____8197  in
                                         (uu____8194,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_false_bool)
                                          in
                                       let arg_exp =
                                         FStar_Syntax_Syntax.bv_to_name
                                           (FStar_Pervasives_Native.fst
                                              unrefined_arg_binder)
                                          in
                                       let uu____8212 =
                                         let uu____8219 =
                                           let uu____8220 =
                                             let uu____8243 =
                                               let uu____8260 =
                                                 FStar_Syntax_Util.branch
                                                   pat_true
                                                  in
                                               let uu____8275 =
                                                 let uu____8292 =
                                                   FStar_Syntax_Util.branch
                                                     pat_false
                                                    in
                                                 [uu____8292]  in
                                               uu____8260 :: uu____8275  in
                                             (arg_exp, uu____8243)  in
                                           FStar_Syntax_Syntax.Tm_match
                                             uu____8220
                                            in
                                         FStar_Syntax_Syntax.mk uu____8219
                                          in
                                       uu____8212
                                         FStar_Pervasives_Native.None p)
                                     in
                                  let dd =
                                    let uu____8368 =
                                      FStar_All.pipe_right quals
                                        (FStar_List.contains
                                           FStar_Syntax_Syntax.Abstract)
                                       in
                                    if uu____8368
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
                                    let uu____8390 =
                                      let uu____8395 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Util.Inr uu____8395  in
                                    let uu____8396 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp
                                       in
                                    FStar_Syntax_Util.mk_letbinding
                                      uu____8390 uvs lbtyp
                                      FStar_Parser_Const.effect_Tot_lid
                                      uu____8396 [] FStar_Range.dummyRange
                                     in
                                  let impl =
                                    let uu____8402 =
                                      let uu____8403 =
                                        let uu____8410 =
                                          let uu____8413 =
                                            let uu____8414 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right
                                               in
                                            FStar_All.pipe_right uu____8414
                                              (fun fv  ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                             in
                                          [uu____8413]  in
                                        ((false, [lb]), uu____8410)  in
                                      FStar_Syntax_Syntax.Sig_let uu____8403
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____8402;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    }  in
                                  (let uu____8428 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "LogTypes")
                                      in
                                   if uu____8428
                                   then
                                     let uu____8432 =
                                       FStar_Syntax_Print.sigelt_to_string
                                         impl
                                        in
                                     FStar_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu____8432
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
                            FStar_Syntax_Util.arg_of_non_null_binder
                              arg_binder
                             in
                          let subst1 =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i  ->
                                    fun uu____8505  ->
                                      match uu____8505 with
                                      | (a,uu____8514) ->
                                          let uu____8519 =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i
                                             in
                                          (match uu____8519 with
                                           | (field_name,uu____8525) ->
                                               let field_proj_tm =
                                                 let uu____8527 =
                                                   let uu____8528 =
                                                     FStar_Syntax_Syntax.lid_as_fv
                                                       field_name
                                                       (FStar_Syntax_Syntax.Delta_equational_at_level
                                                          Prims.int_one)
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Syntax.fv_to_tm
                                                     uu____8528
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   uu____8527 inst_univs
                                                  in
                                               let proj =
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   field_proj_tm [arg]
                                                   FStar_Pervasives_Native.None
                                                   p
                                                  in
                                               FStar_Syntax_Syntax.NT
                                                 (a, proj))))
                             in
                          let projectors_ses =
                            let uu____8554 =
                              FStar_All.pipe_right fields
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____8596  ->
                                        match uu____8596 with
                                        | (x,uu____8607) ->
                                            let p1 =
                                              FStar_Syntax_Syntax.range_of_bv
                                                x
                                               in
                                            let uu____8613 =
                                              FStar_Syntax_Util.mk_field_projector_name
                                                lid x i
                                               in
                                            (match uu____8613 with
                                             | (field_name,uu____8621) ->
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
                                                   let uu____8634 =
                                                     FStar_Syntax_Util.arrow
                                                       binders result_comp
                                                      in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.close_univ_vars
                                                        uvs) uu____8634
                                                    in
                                                 let only_decl =
                                                   early_prims_inductive ||
                                                     (let uu____8640 =
                                                        let uu____8642 =
                                                          FStar_TypeChecker_Env.current_module
                                                            env
                                                           in
                                                        uu____8642.FStar_Ident.str
                                                         in
                                                      FStar_Options.dont_gen_projectors
                                                        uu____8640)
                                                    in
                                                 let no_decl = false  in
                                                 let quals q =
                                                   if only_decl
                                                   then
                                                     let uu____8661 =
                                                       FStar_List.filter
                                                         (fun uu___5_8665  ->
                                                            match uu___5_8665
                                                            with
                                                            | FStar_Syntax_Syntax.Abstract
                                                                 -> false
                                                            | uu____8668 ->
                                                                true) q
                                                        in
                                                     FStar_Syntax_Syntax.Assumption
                                                       :: uu____8661
                                                   else q  in
                                                 let quals1 =
                                                   let iquals1 =
                                                     FStar_All.pipe_right
                                                       iquals
                                                       (FStar_List.filter
                                                          (fun uu___6_8683 
                                                             ->
                                                             match uu___6_8683
                                                             with
                                                             | FStar_Syntax_Syntax.Inline_for_extraction
                                                                  -> true
                                                             | FStar_Syntax_Syntax.NoExtract
                                                                  -> true
                                                             | FStar_Syntax_Syntax.Abstract
                                                                  -> true
                                                             | FStar_Syntax_Syntax.Private
                                                                  -> true
                                                             | uu____8689 ->
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
                                                   let uu____8700 =
                                                     FStar_Ident.range_of_lid
                                                       field_name
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                                          (field_name, uvs,
                                                            t));
                                                     FStar_Syntax_Syntax.sigrng
                                                       = uu____8700;
                                                     FStar_Syntax_Syntax.sigquals
                                                       = quals1;
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       FStar_Syntax_Syntax.default_sigmeta;
                                                     FStar_Syntax_Syntax.sigattrs
                                                       = attrs1;
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       FStar_Pervasives_Native.None
                                                   }  in
                                                 ((let uu____8702 =
                                                     FStar_TypeChecker_Env.debug
                                                       env
                                                       (FStar_Options.Other
                                                          "LogTypes")
                                                      in
                                                   if uu____8702
                                                   then
                                                     let uu____8706 =
                                                       FStar_Syntax_Print.sigelt_to_string
                                                         decl
                                                        in
                                                     FStar_Util.print1
                                                       "Declaration of a projector %s\n"
                                                       uu____8706
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
                                                               fun uu____8760
                                                                  ->
                                                                 match uu____8760
                                                                 with
                                                                 | (x1,imp)
                                                                    ->
                                                                    let b =
                                                                    FStar_Syntax_Syntax.is_implicit
                                                                    imp  in
                                                                    if
                                                                    (i + ntps)
                                                                    = j
                                                                    then
                                                                    let uu____8786
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                    (uu____8786,
                                                                    b)
                                                                    else
                                                                    if
                                                                    b &&
                                                                    (j < ntps)
                                                                    then
                                                                    (let uu____8802
                                                                    =
                                                                    let uu____8805
                                                                    =
                                                                    let uu____8806
                                                                    =
                                                                    let uu____8813
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8813,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8806
                                                                     in
                                                                    pos
                                                                    uu____8805
                                                                     in
                                                                    (uu____8802,
                                                                    b))
                                                                    else
                                                                    (let uu____8821
                                                                    =
                                                                    let uu____8824
                                                                    =
                                                                    let uu____8825
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8825
                                                                     in
                                                                    pos
                                                                    uu____8824
                                                                     in
                                                                    (uu____8821,
                                                                    b))))
                                                        in
                                                     let pat =
                                                       let uu____8844 =
                                                         let uu____8847 =
                                                           let uu____8848 =
                                                             let uu____8862 =
                                                               FStar_Syntax_Syntax.lid_as_fv
                                                                 lid
                                                                 FStar_Syntax_Syntax.delta_constant
                                                                 (FStar_Pervasives_Native.Some
                                                                    fvq)
                                                                in
                                                             (uu____8862,
                                                               arg_pats)
                                                              in
                                                           FStar_Syntax_Syntax.Pat_cons
                                                             uu____8848
                                                            in
                                                         pos uu____8847  in
                                                       let uu____8872 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           projection
                                                          in
                                                       (uu____8844,
                                                         FStar_Pervasives_Native.None,
                                                         uu____8872)
                                                        in
                                                     let body =
                                                       let uu____8888 =
                                                         let uu____8895 =
                                                           let uu____8896 =
                                                             let uu____8919 =
                                                               let uu____8936
                                                                 =
                                                                 FStar_Syntax_Util.branch
                                                                   pat
                                                                  in
                                                               [uu____8936]
                                                                in
                                                             (arg_exp,
                                                               uu____8919)
                                                              in
                                                           FStar_Syntax_Syntax.Tm_match
                                                             uu____8896
                                                            in
                                                         FStar_Syntax_Syntax.mk
                                                           uu____8895
                                                          in
                                                       uu____8888
                                                         FStar_Pervasives_Native.None
                                                         p1
                                                        in
                                                     let imp =
                                                       FStar_Syntax_Util.abs
                                                         binders body
                                                         FStar_Pervasives_Native.None
                                                        in
                                                     let dd =
                                                       let uu____9001 =
                                                         FStar_All.pipe_right
                                                           quals1
                                                           (FStar_List.contains
                                                              FStar_Syntax_Syntax.Abstract)
                                                          in
                                                       if uu____9001
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
                                                       let uu____9020 =
                                                         let uu____9025 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             field_name dd
                                                             FStar_Pervasives_Native.None
                                                            in
                                                         FStar_Util.Inr
                                                           uu____9025
                                                          in
                                                       let uu____9026 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           uvs imp
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.lbname
                                                           = uu____9020;
                                                         FStar_Syntax_Syntax.lbunivs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.lbtyp
                                                           = lbtyp;
                                                         FStar_Syntax_Syntax.lbeff
                                                           =
                                                           FStar_Parser_Const.effect_Tot_lid;
                                                         FStar_Syntax_Syntax.lbdef
                                                           = uu____9026;
                                                         FStar_Syntax_Syntax.lbattrs
                                                           = [];
                                                         FStar_Syntax_Syntax.lbpos
                                                           =
                                                           FStar_Range.dummyRange
                                                       }  in
                                                     let impl =
                                                       let uu____9032 =
                                                         let uu____9033 =
                                                           let uu____9040 =
                                                             let uu____9043 =
                                                               let uu____9044
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   lb.FStar_Syntax_Syntax.lbname
                                                                   FStar_Util.right
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____9044
                                                                 (fun fv  ->
                                                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                                in
                                                             [uu____9043]  in
                                                           ((false, [lb]),
                                                             uu____9040)
                                                            in
                                                         FStar_Syntax_Syntax.Sig_let
                                                           uu____9033
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.sigel
                                                           = uu____9032;
                                                         FStar_Syntax_Syntax.sigrng
                                                           = p1;
                                                         FStar_Syntax_Syntax.sigquals
                                                           = quals1;
                                                         FStar_Syntax_Syntax.sigmeta
                                                           =
                                                           FStar_Syntax_Syntax.default_sigmeta;
                                                         FStar_Syntax_Syntax.sigattrs
                                                           = attrs1;
                                                         FStar_Syntax_Syntax.sigopts
                                                           =
                                                           FStar_Pervasives_Native.None
                                                       }  in
                                                     (let uu____9058 =
                                                        FStar_TypeChecker_Env.debug
                                                          env
                                                          (FStar_Options.Other
                                                             "LogTypes")
                                                         in
                                                      if uu____9058
                                                      then
                                                        let uu____9062 =
                                                          FStar_Syntax_Print.sigelt_to_string
                                                            impl
                                                           in
                                                        FStar_Util.print1
                                                          "Implementation of a projector %s\n"
                                                          uu____9062
                                                      else ());
                                                     if no_decl
                                                     then [impl]
                                                     else [decl; impl])))))
                               in
                            FStar_All.pipe_right uu____8554
                              FStar_List.flatten
                             in
                          FStar_List.append discriminator_ses projectors_ses
  
let (mk_data_operations :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.sigelt Prims.list ->
          FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun attrs  ->
      fun env  ->
        fun tcs  ->
          fun se  ->
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_datacon
                (constr_lid,uvs,t,typ_lid,n_typars,uu____9125) when
                let uu____9132 =
                  FStar_Ident.lid_equals constr_lid
                    FStar_Parser_Const.lexcons_lid
                   in
                Prims.op_Negation uu____9132 ->
                let uu____9134 = FStar_Syntax_Subst.univ_var_opening uvs  in
                (match uu____9134 with
                 | (univ_opening,uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                     let uu____9156 = FStar_Syntax_Util.arrow_formals t1  in
                     (match uu____9156 with
                      | (formals,uu____9174) ->
                          let uu____9195 =
                            let tps_opt =
                              FStar_Util.find_map tcs
                                (fun se1  ->
                                   let uu____9230 =
                                     let uu____9232 =
                                       let uu____9233 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____9233  in
                                     FStar_Ident.lid_equals typ_lid
                                       uu____9232
                                      in
                                   if uu____9230
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu____9255,uvs',tps,typ0,uu____9259,constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_List.length constrs) >
                                                Prims.int_one))
                                     | uu____9279 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None)
                               in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                let uu____9328 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid
                                   in
                                if uu____9328
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng
                             in
                          (match uu____9195 with
                           | (inductive_tps,typ0,should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps
                                  in
                               let typ01 =
                                 FStar_Syntax_Subst.subst univ_opening typ0
                                  in
                               let uu____9366 =
                                 FStar_Syntax_Util.arrow_formals typ01  in
                               (match uu____9366 with
                                | (indices,uu____9384) ->
                                    let refine_domain =
                                      let uu____9407 =
                                        FStar_All.pipe_right
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Util.for_some
                                             (fun uu___7_9414  ->
                                                match uu___7_9414 with
                                                | FStar_Syntax_Syntax.RecordConstructor
                                                    uu____9416 -> true
                                                | uu____9426 -> false))
                                         in
                                      if uu____9407
                                      then false
                                      else should_refine  in
                                    let fv_qual =
                                      let filter_records uu___8_9441 =
                                        match uu___8_9441 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu____9444,fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (constr_lid, fns))
                                        | uu____9456 ->
                                            FStar_Pervasives_Native.None
                                         in
                                      let uu____9457 =
                                        FStar_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records
                                         in
                                      match uu____9457 with
                                      | FStar_Pervasives_Native.None  ->
                                          FStar_Syntax_Syntax.Data_ctor
                                      | FStar_Pervasives_Native.Some q -> q
                                       in
                                    let iquals1 =
                                      if
                                        (FStar_List.contains
                                           FStar_Syntax_Syntax.Abstract
                                           iquals)
                                          &&
                                          (Prims.op_Negation
                                             (FStar_List.contains
                                                FStar_Syntax_Syntax.Private
                                                iquals))
                                      then FStar_Syntax_Syntax.Private ::
                                        iquals
                                      else iquals  in
                                    let fields =
                                      let uu____9470 =
                                        FStar_Util.first_N n_typars formals
                                         in
                                      match uu____9470 with
                                      | (imp_tps,fields) ->
                                          let rename =
                                            FStar_List.map2
                                              (fun uu____9553  ->
                                                 fun uu____9554  ->
                                                   match (uu____9553,
                                                           uu____9554)
                                                   with
                                                   | ((x,uu____9580),
                                                      (x',uu____9582)) ->
                                                       let uu____9603 =
                                                         let uu____9610 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x'
                                                            in
                                                         (x, uu____9610)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____9603) imp_tps
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
                                      iquals1 attrs fv_qual refine_domain env
                                      typ_lid constr_lid uvs1 inductive_tps1
                                      indices fields erasable1))))
            | uu____9617 -> []
  