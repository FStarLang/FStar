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
                                      let subst =
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
                                        let uu____965 =
                                          FStar_Syntax_Subst.subst subst t3
                                           in
                                        FStar_Syntax_Util.arrow_formals_comp
                                          uu____965
                                         in
                                      (match uu____960 with
                                       | (bs1,c1) ->
                                           let uu____974 =
                                             (FStar_Options.ml_ish ()) ||
                                               (FStar_Syntax_Util.is_total_comp
                                                  c1)
                                              in
                                           if uu____974
                                           then
                                             (bs1,
                                               (FStar_Syntax_Util.comp_result
                                                  c1))
                                           else
                                             (let uu____987 =
                                                FStar_Ident.range_of_lid
                                                  (FStar_Syntax_Util.comp_effect_name
                                                     c1)
                                                 in
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                  "Constructors cannot have effects")
                                                uu____987)))
                             | uu____996 -> ([], t2)  in
                           (match uu____800 with
                            | (arguments,result) ->
                                ((let uu____1016 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Low
                                     in
                                  if uu____1016
                                  then
                                    let uu____1019 =
                                      FStar_Syntax_Print.lid_to_string c  in
                                    let uu____1021 =
                                      FStar_Syntax_Print.binders_to_string
                                        "->" arguments
                                       in
                                    let uu____1024 =
                                      FStar_Syntax_Print.term_to_string
                                        result
                                       in
                                    FStar_Util.print3
                                      "Checking datacon  %s : %s -> %s \n"
                                      uu____1019 uu____1021 uu____1024
                                  else ());
                                 (let uu____1029 =
                                    FStar_TypeChecker_TcTerm.tc_tparams env2
                                      arguments
                                     in
                                  match uu____1029 with
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
                                      let uu____1047 =
                                        FStar_TypeChecker_TcTerm.tc_trivial_guard
                                          env'1 result
                                         in
                                      (match uu____1047 with
                                       | (result1,res_lcomp) ->
                                           let uu____1058 =
                                             FStar_Syntax_Util.head_and_args
                                               result1
                                              in
                                           (match uu____1058 with
                                            | (head,args) ->
                                                let p_args =
                                                  let uu____1116 =
                                                    FStar_Util.first_N
                                                      (FStar_List.length tps)
                                                      args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____1116
                                                   in
                                                (FStar_List.iter2
                                                   (fun uu____1198  ->
                                                      fun uu____1199  ->
                                                        match (uu____1198,
                                                                uu____1199)
                                                        with
                                                        | ((bv,uu____1229),
                                                           (t2,uu____1231))
                                                            ->
                                                            let uu____1258 =
                                                              let uu____1259
                                                                =
                                                                FStar_Syntax_Subst.compress
                                                                  t2
                                                                 in
                                                              uu____1259.FStar_Syntax_Syntax.n
                                                               in
                                                            (match uu____1258
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_name
                                                                 bv' when
                                                                 FStar_Syntax_Syntax.bv_eq
                                                                   bv bv'
                                                                 -> ()
                                                             | uu____1263 ->
                                                                 let uu____1264
                                                                   =
                                                                   let uu____1270
                                                                    =
                                                                    let uu____1272
                                                                    =
                                                                    FStar_Syntax_Print.bv_to_string
                                                                    bv  in
                                                                    let uu____1274
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    FStar_Util.format2
                                                                    "This parameter is not constant: expected %s, got %s"
                                                                    uu____1272
                                                                    uu____1274
                                                                     in
                                                                   (FStar_Errors.Error_BadInductiveParam,
                                                                    uu____1270)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____1264
                                                                   t2.FStar_Syntax_Syntax.pos))
                                                   tps p_args;
                                                 (let ty =
                                                    let uu____1279 =
                                                      unfold_whnf env2
                                                        res_lcomp.FStar_TypeChecker_Common.res_typ
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1279
                                                      FStar_Syntax_Util.unrefine
                                                     in
                                                  (let uu____1281 =
                                                     let uu____1282 =
                                                       FStar_Syntax_Subst.compress
                                                         ty
                                                        in
                                                     uu____1282.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____1281 with
                                                   | FStar_Syntax_Syntax.Tm_type
                                                       uu____1285 -> ()
                                                   | uu____1286 ->
                                                       let uu____1287 =
                                                         let uu____1293 =
                                                           let uu____1295 =
                                                             FStar_Syntax_Print.term_to_string
                                                               result1
                                                              in
                                                           let uu____1297 =
                                                             FStar_Syntax_Print.term_to_string
                                                               ty
                                                              in
                                                           FStar_Util.format2
                                                             "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                             uu____1295
                                                             uu____1297
                                                            in
                                                         (FStar_Errors.Fatal_WrongResultTypeAfterConstrutor,
                                                           uu____1293)
                                                          in
                                                       FStar_Errors.raise_error
                                                         uu____1287
                                                         se.FStar_Syntax_Syntax.sigrng);
                                                  (let g_uvs =
                                                     let uu____1302 =
                                                       let uu____1303 =
                                                         FStar_Syntax_Subst.compress
                                                           head
                                                          in
                                                       uu____1303.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____1302 with
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____1307;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____1308;_},tuvs)
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
                                                                    let uu____1322
                                                                    =
                                                                    let uu____1323
                                                                    =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_type
                                                                    u1)
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange
                                                                     in
                                                                    let uu____1324
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
                                                                    uu____1323
                                                                    uu____1324
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1322)
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
                                                     | uu____1330 ->
                                                         let uu____1331 =
                                                           let uu____1337 =
                                                             let uu____1339 =
                                                               FStar_Syntax_Print.lid_to_string
                                                                 tc_lid
                                                                in
                                                             let uu____1341 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 head
                                                                in
                                                             FStar_Util.format2
                                                               "Expected a constructor of type %s; got %s"
                                                               uu____1339
                                                               uu____1341
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedConstructorType,
                                                             uu____1337)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____1331
                                                           se.FStar_Syntax_Syntax.sigrng
                                                      in
                                                   let g =
                                                     FStar_List.fold_left2
                                                       (fun g  ->
                                                          fun uu____1359  ->
                                                            fun u_x  ->
                                                              match uu____1359
                                                              with
                                                              | (x,uu____1368)
                                                                  ->
                                                                  let uu____1373
                                                                    =
                                                                    FStar_TypeChecker_Rel.universe_inequality
                                                                    u_x u_tc
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g
                                                                    uu____1373)
                                                       g_uvs arguments1 us
                                                      in
                                                   let t2 =
                                                     let uu____1377 =
                                                       let uu____1386 =
                                                         FStar_All.pipe_right
                                                           tps
                                                           (FStar_List.map
                                                              (fun uu____1426
                                                                  ->
                                                                 match uu____1426
                                                                 with
                                                                 | (x,uu____1440)
                                                                    ->
                                                                    (x,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    true)))))
                                                          in
                                                       FStar_List.append
                                                         uu____1386
                                                         arguments1
                                                        in
                                                     let uu____1454 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         result1
                                                        in
                                                     FStar_Syntax_Util.arrow
                                                       uu____1377 uu____1454
                                                      in
                                                   let t3 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       _uvs1 t2
                                                      in
                                                   ((let uu___187_1459 = se
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
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigrng);
                                                       FStar_Syntax_Syntax.sigquals
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigquals);
                                                       FStar_Syntax_Syntax.sigmeta
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigmeta);
                                                       FStar_Syntax_Syntax.sigattrs
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigattrs);
                                                       FStar_Syntax_Syntax.sigopts
                                                         =
                                                         (uu___187_1459.FStar_Syntax_Syntax.sigopts)
                                                     }), g))))))))))))
        | uu____1463 -> failwith "impossible"
  
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
               (fun uu____1554  ->
                  match uu____1554 with
                  | (se,uu____1560) ->
                      (match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (uu____1561,uu____1562,tps,k,uu____1565,uu____1566)
                           ->
                           let uu____1575 =
                             let uu____1576 = FStar_Syntax_Syntax.mk_Total k
                                in
                             FStar_All.pipe_left
                               (FStar_Syntax_Util.arrow tps) uu____1576
                              in
                           FStar_Syntax_Syntax.null_binder uu____1575
                       | uu____1581 -> failwith "Impossible")))
           in
        let binders' =
          FStar_All.pipe_right datas
            (FStar_List.map
               (fun se  ->
                  match se.FStar_Syntax_Syntax.sigel with
                  | FStar_Syntax_Syntax.Sig_datacon
                      (uu____1610,uu____1611,t,uu____1613,uu____1614,uu____1615)
                      -> FStar_Syntax_Syntax.null_binder t
                  | uu____1622 -> failwith "Impossible"))
           in
        let t =
          let uu____1627 =
            FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.t_unit  in
          FStar_Syntax_Util.arrow (FStar_List.append binders binders')
            uu____1627
           in
        (let uu____1637 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "GenUniverses")
            in
         if uu____1637
         then
           let uu____1642 = FStar_TypeChecker_Normalize.term_to_string env t
              in
           FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n"
             uu____1642
         else ());
        (let uu____1647 = FStar_TypeChecker_Util.generalize_universes env t
            in
         match uu____1647 with
         | (uvs,t1) ->
             ((let uu____1667 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "GenUniverses")
                  in
               if uu____1667
               then
                 let uu____1672 =
                   let uu____1674 =
                     FStar_All.pipe_right uvs
                       (FStar_List.map (fun u  -> u.FStar_Ident.idText))
                      in
                   FStar_All.pipe_right uu____1674 (FStar_String.concat ", ")
                    in
                 let uu____1691 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n"
                   uu____1672 uu____1691
               else ());
              (let uu____1696 = FStar_Syntax_Subst.open_univ_vars uvs t1  in
               match uu____1696 with
               | (uvs1,t2) ->
                   let uu____1711 = FStar_Syntax_Util.arrow_formals t2  in
                   (match uu____1711 with
                    | (args,uu____1727) ->
                        let uu____1732 =
                          FStar_Util.first_N (FStar_List.length binders) args
                           in
                        (match uu____1732 with
                         | (tc_types,data_types) ->
                             let tcs1 =
                               FStar_List.map2
                                 (fun uu____1837  ->
                                    fun uu____1838  ->
                                      match (uu____1837, uu____1838) with
                                      | ((x,uu____1860),(se,uu____1862)) ->
                                          (match se.FStar_Syntax_Syntax.sigel
                                           with
                                           | FStar_Syntax_Syntax.Sig_inductive_typ
                                               (tc,uu____1878,tps,uu____1880,mutuals,datas1)
                                               ->
                                               let ty =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs1
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let uu____1892 =
                                                 let uu____1897 =
                                                   let uu____1898 =
                                                     FStar_Syntax_Subst.compress
                                                       ty
                                                      in
                                                   uu____1898.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____1897 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (binders1,c) ->
                                                     let uu____1927 =
                                                       FStar_Util.first_N
                                                         (FStar_List.length
                                                            tps) binders1
                                                        in
                                                     (match uu____1927 with
                                                      | (tps1,rest) ->
                                                          let t3 =
                                                            match rest with
                                                            | [] ->
                                                                FStar_Syntax_Util.comp_result
                                                                  c
                                                            | uu____2005 ->
                                                                FStar_Syntax_Syntax.mk
                                                                  (FStar_Syntax_Syntax.Tm_arrow
                                                                    (rest, c))
                                                                  FStar_Pervasives_Native.None
                                                                  (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                             in
                                                          (tps1, t3))
                                                 | uu____2024 -> ([], ty)  in
                                               (match uu____1892 with
                                                | (tps1,t3) ->
                                                    let uu___264_2033 = se
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
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigrng);
                                                      FStar_Syntax_Syntax.sigquals
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigquals);
                                                      FStar_Syntax_Syntax.sigmeta
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigmeta);
                                                      FStar_Syntax_Syntax.sigattrs
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigattrs);
                                                      FStar_Syntax_Syntax.sigopts
                                                        =
                                                        (uu___264_2033.FStar_Syntax_Syntax.sigopts)
                                                    })
                                           | uu____2038 ->
                                               failwith "Impossible"))
                                 tc_types tcs
                                in
                             let datas1 =
                               match uvs1 with
                               | [] -> datas
                               | uu____2045 ->
                                   let uvs_universes =
                                     FStar_All.pipe_right uvs1
                                       (FStar_List.map
                                          (fun uu____2049  ->
                                             FStar_Syntax_Syntax.U_name
                                               uu____2049))
                                      in
                                   let tc_insts =
                                     FStar_All.pipe_right tcs1
                                       (FStar_List.map
                                          (fun uu___0_2069  ->
                                             match uu___0_2069 with
                                             | {
                                                 FStar_Syntax_Syntax.sigel =
                                                   FStar_Syntax_Syntax.Sig_inductive_typ
                                                   (tc,uu____2075,uu____2076,uu____2077,uu____2078,uu____2079);
                                                 FStar_Syntax_Syntax.sigrng =
                                                   uu____2080;
                                                 FStar_Syntax_Syntax.sigquals
                                                   = uu____2081;
                                                 FStar_Syntax_Syntax.sigmeta
                                                   = uu____2082;
                                                 FStar_Syntax_Syntax.sigattrs
                                                   = uu____2083;
                                                 FStar_Syntax_Syntax.sigopts
                                                   = uu____2084;_}
                                                 -> (tc, uvs_universes)
                                             | uu____2099 ->
                                                 failwith "Impossible"))
                                      in
                                   FStar_List.map2
                                     (fun uu____2123  ->
                                        fun d  ->
                                          match uu____2123 with
                                          | (t3,uu____2132) ->
                                              (match d.FStar_Syntax_Syntax.sigel
                                               with
                                               | FStar_Syntax_Syntax.Sig_datacon
                                                   (l,uu____2138,uu____2139,tc,ntps,mutuals)
                                                   ->
                                                   let ty =
                                                     let uu____2150 =
                                                       FStar_Syntax_InstFV.instantiate
                                                         tc_insts
                                                         t3.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2150
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          uvs1)
                                                      in
                                                   let uu___301_2151 = d  in
                                                   {
                                                     FStar_Syntax_Syntax.sigel
                                                       =
                                                       (FStar_Syntax_Syntax.Sig_datacon
                                                          (l, uvs1, ty, tc,
                                                            ntps, mutuals));
                                                     FStar_Syntax_Syntax.sigrng
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigrng);
                                                     FStar_Syntax_Syntax.sigquals
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigquals);
                                                     FStar_Syntax_Syntax.sigmeta
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigmeta);
                                                     FStar_Syntax_Syntax.sigattrs
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigattrs);
                                                     FStar_Syntax_Syntax.sigopts
                                                       =
                                                       (uu___301_2151.FStar_Syntax_Syntax.sigopts)
                                                   }
                                               | uu____2155 ->
                                                   failwith "Impossible"))
                                     data_types datas
                                in
                             (tcs1, datas1))))))
  
let (debug_log :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env  ->
    fun msg  ->
      let uu____2179 =
        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity")
         in
      if uu____2179
      then
        let uu____2184 =
          let uu____2186 =
            let uu____2188 = msg ()  in Prims.op_Hat uu____2188 "\n"  in
          Prims.op_Hat "Positivity::" uu____2186  in
        FStar_Util.print_string uu____2184
      else ()
  
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid  ->
    fun t  ->
      let uu____2207 = FStar_Syntax_Free.fvars t  in
      FStar_Util.set_mem ty_lid uu____2207
  
let rec (try_get_fv :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____2228 =
      let uu____2229 = FStar_Syntax_Subst.compress t  in
      uu____2229.FStar_Syntax_Syntax.n  in
    match uu____2228 with
    | FStar_Syntax_Syntax.Tm_name uu____2238 -> FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Pervasives_Native.Some (fv, [])
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____2254 =
          let uu____2255 = FStar_Syntax_Subst.compress t1  in
          uu____2255.FStar_Syntax_Syntax.n  in
        (match uu____2254 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, us)
         | uu____2269 ->
             failwith
               "try_get_fv: Node is a Tm_uinst, but Tm_uinst is not an fvar")
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2278,uu____2279) ->
        try_get_fv t1
    | uu____2320 ->
        let uu____2321 =
          let uu____2323 = FStar_Syntax_Print.tag_of_term t  in
          Prims.op_Hat "try_get_fv: did not expect t to be a : " uu____2323
           in
        failwith uu____2321
  
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
          let uu____2363 = FStar_ST.op_Bang unfolded  in
          FStar_List.existsML
            (fun uu____2412  ->
               match uu____2412 with
               | (lid,l) ->
                   (FStar_Ident.lid_equals lid ilid) &&
                     (let args =
                        let uu____2456 =
                          FStar_List.splitAt (FStar_List.length l) arrghs  in
                        FStar_Pervasives_Native.fst uu____2456  in
                      FStar_List.fold_left2
                        (fun b  ->
                           fun a  ->
                             fun a'  ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args l)) uu____2363
  
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
            (fun uu____2663  ->
               let uu____2664 = FStar_Syntax_Print.term_to_string btype  in
               Prims.op_Hat "Checking strict positivity in type: " uu____2664);
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
             (fun uu____2671  ->
                let uu____2672 = FStar_Syntax_Print.term_to_string btype1  in
                Prims.op_Hat
                  "Checking strict positivity in type, after normalization: "
                  uu____2672);
           (let uu____2677 = ty_occurs_in ty_lid btype1  in
            Prims.op_Negation uu____2677) ||
             ((debug_log env
                 (fun uu____2687  ->
                    "ty does occur in this type, pressing ahead");
               (let uu____2689 =
                  let uu____2690 = FStar_Syntax_Subst.compress btype1  in
                  uu____2690.FStar_Syntax_Syntax.n  in
                match uu____2689 with
                | FStar_Syntax_Syntax.Tm_app (t,args) ->
                    let fv_us_opt = try_get_fv t  in
                    let uu____2727 =
                      FStar_All.pipe_right fv_us_opt FStar_Util.is_none  in
                    if uu____2727
                    then true
                    else
                      (let uu____2745 =
                         FStar_All.pipe_right fv_us_opt FStar_Util.must  in
                       match uu____2745 with
                       | (fv,us) ->
                           let uu____2767 =
                             FStar_Ident.lid_equals
                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               ty_lid
                              in
                           if uu____2767
                           then
                             (debug_log env
                                (fun uu____2773  ->
                                   "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
                              FStar_List.for_all
                                (fun uu____2785  ->
                                   match uu____2785 with
                                   | (t1,uu____2794) ->
                                       let uu____2799 =
                                         ty_occurs_in ty_lid t1  in
                                       Prims.op_Negation uu____2799) args)
                           else
                             (debug_log env
                                (fun uu____2805  ->
                                   "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
                              ty_nested_positive_in_inductive ty_lid
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                us args unfolded env))
                | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                    (debug_log env
                       (fun uu____2831  ->
                          "Checking strict positivity in Tm_arrow");
                     (let check_comp =
                        let c1 =
                          let uu____2838 =
                            FStar_TypeChecker_Env.unfold_effect_abbrev env c
                             in
                          FStar_All.pipe_right uu____2838
                            FStar_Syntax_Syntax.mk_Comp
                           in
                        (FStar_Syntax_Util.is_pure_or_ghost_comp c1) ||
                          (let uu____2842 =
                             FStar_TypeChecker_Env.lookup_effect_quals env
                               (FStar_Syntax_Util.comp_effect_name c1)
                              in
                           FStar_All.pipe_right uu____2842
                             (FStar_List.existsb
                                (fun q  ->
                                   q = FStar_Syntax_Syntax.TotalEffect)))
                         in
                      if Prims.op_Negation check_comp
                      then
                        (debug_log env
                           (fun uu____2854  ->
                              "Checking strict positivity , the arrow is impure, so return true");
                         true)
                      else
                        (debug_log env
                           (fun uu____2861  ->
                              "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                         (FStar_List.for_all
                            (fun uu____2873  ->
                               match uu____2873 with
                               | (b,uu____2882) ->
                                   let uu____2887 =
                                     ty_occurs_in ty_lid
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   Prims.op_Negation uu____2887) sbs)
                           &&
                           ((let uu____2893 =
                               FStar_Syntax_Subst.open_term sbs
                                 (FStar_Syntax_Util.comp_result c)
                                in
                             match uu____2893 with
                             | (uu____2899,return_type) ->
                                 let uu____2901 =
                                   FStar_TypeChecker_Env.push_binders env sbs
                                    in
                                 ty_strictly_positive_in_type ty_lid
                                   return_type unfolded uu____2901)))))
                | FStar_Syntax_Syntax.Tm_fvar uu____2902 ->
                    (debug_log env
                       (fun uu____2905  ->
                          "Checking strict positivity in an fvar, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_type uu____2908 ->
                    (debug_log env
                       (fun uu____2911  ->
                          "Checking strict positivity in an Tm_type, return true");
                     true)
                | FStar_Syntax_Syntax.Tm_uinst (t,uu____2915) ->
                    (debug_log env
                       (fun uu____2922  ->
                          "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | FStar_Syntax_Syntax.Tm_refine (bv,uu____2925) ->
                    (debug_log env
                       (fun uu____2932  ->
                          "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                     ty_strictly_positive_in_type ty_lid
                       bv.FStar_Syntax_Syntax.sort unfolded env)
                | FStar_Syntax_Syntax.Tm_match (uu____2934,branches) ->
                    (debug_log env
                       (fun uu____2974  ->
                          "Checking strict positivity in an Tm_match, recur in the branches)");
                     FStar_List.for_all
                       (fun uu____2995  ->
                          match uu____2995 with
                          | (p,uu____3008,t) ->
                              let bs =
                                let uu____3027 =
                                  FStar_Syntax_Syntax.pat_bvs p  in
                                FStar_List.map FStar_Syntax_Syntax.mk_binder
                                  uu____3027
                                 in
                              let uu____3036 =
                                FStar_Syntax_Subst.open_term bs t  in
                              (match uu____3036 with
                               | (bs1,t1) ->
                                   let uu____3044 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs1
                                      in
                                   ty_strictly_positive_in_type ty_lid t1
                                     unfolded uu____3044)) branches)
                | FStar_Syntax_Syntax.Tm_ascribed (t,uu____3046,uu____3047)
                    ->
                    (debug_log env
                       (fun uu____3090  ->
                          "Checking strict positivity in an Tm_ascribed, recur)");
                     ty_strictly_positive_in_type ty_lid t unfolded env)
                | uu____3092 ->
                    (debug_log env
                       (fun uu____3096  ->
                          let uu____3097 =
                            let uu____3099 =
                              FStar_Syntax_Print.tag_of_term btype1  in
                            let uu____3101 =
                              let uu____3103 =
                                FStar_Syntax_Print.term_to_string btype1  in
                              Prims.op_Hat " and term: " uu____3103  in
                            Prims.op_Hat uu____3099 uu____3101  in
                          Prims.op_Hat
                            "Checking strict positivity, unexpected tag: "
                            uu____3097);
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
                (fun uu____3118  ->
                   let uu____3119 =
                     let uu____3121 =
                       let uu____3123 =
                         FStar_Syntax_Print.args_to_string args  in
                       Prims.op_Hat " applied to arguments: " uu____3123  in
                     Prims.op_Hat ilid.FStar_Ident.str uu____3121  in
                   Prims.op_Hat
                     "Checking nested positivity in the inductive "
                     uu____3119);
              (let uu____3127 =
                 FStar_TypeChecker_Env.datacons_of_typ env ilid  in
               match uu____3127 with
               | (b,idatas) ->
                   if Prims.op_Negation b
                   then
                     let uu____3146 =
                       let uu____3148 =
                         FStar_Syntax_Syntax.lid_as_fv ilid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None
                          in
                       FStar_TypeChecker_Env.fv_has_attr env uu____3148
                         FStar_Parser_Const.assume_strictly_positive_attr_lid
                        in
                     (if uu____3146
                      then
                        (debug_log env
                           (fun uu____3154  ->
                              let uu____3155 = FStar_Ident.string_of_lid ilid
                                 in
                              FStar_Util.format1
                                "Checking nested positivity, special case decorated with `assume_strictly_positive` %s; return true"
                                uu____3155);
                         true)
                      else
                        (debug_log env
                           (fun uu____3163  ->
                              "Checking nested positivity, not an inductive, return false");
                         false))
                   else
                     (let uu____3168 =
                        already_unfolded ilid args unfolded env  in
                      if uu____3168
                      then
                        (debug_log env
                           (fun uu____3174  ->
                              "Checking nested positivity, we have already unfolded this inductive with these args");
                         true)
                      else
                        (let num_ibs =
                           let uu____3181 =
                             FStar_TypeChecker_Env.num_inductive_ty_params
                               env ilid
                              in
                           FStar_Option.get uu____3181  in
                         debug_log env
                           (fun uu____3189  ->
                              let uu____3190 =
                                let uu____3192 =
                                  FStar_Util.string_of_int num_ibs  in
                                Prims.op_Hat uu____3192
                                  ", also adding to the memo table"
                                 in
                              Prims.op_Hat
                                "Checking nested positivity, number of type parameters is "
                                uu____3190);
                         (let uu____3197 =
                            let uu____3198 = FStar_ST.op_Bang unfolded  in
                            let uu____3224 =
                              let uu____3231 =
                                let uu____3236 =
                                  let uu____3237 =
                                    FStar_List.splitAt num_ibs args  in
                                  FStar_Pervasives_Native.fst uu____3237  in
                                (ilid, uu____3236)  in
                              [uu____3231]  in
                            FStar_List.append uu____3198 uu____3224  in
                          FStar_ST.op_Colon_Equals unfolded uu____3197);
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
                    (fun uu____3335  ->
                       Prims.op_Hat
                         "Checking nested positivity in data constructor "
                         (Prims.op_Hat dlid.FStar_Ident.str
                            (Prims.op_Hat " of the inductive "
                               ilid.FStar_Ident.str)));
                  (let uu____3338 =
                     FStar_TypeChecker_Env.lookup_datacon env dlid  in
                   match uu____3338 with
                   | (univ_unif_vars,dt) ->
                       (FStar_List.iter2
                          (fun u'  ->
                             fun u  ->
                               match u' with
                               | FStar_Syntax_Syntax.U_unif u'' ->
                                   FStar_Syntax_Unionfind.univ_change u'' u
                               | uu____3361 ->
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
                           (fun uu____3367  ->
                              let uu____3368 =
                                FStar_Syntax_Print.term_to_string dt1  in
                              Prims.op_Hat
                                "Checking nested positivity in the data constructor type: "
                                uu____3368);
                         (let uu____3371 =
                            let uu____3372 = FStar_Syntax_Subst.compress dt1
                               in
                            uu____3372.FStar_Syntax_Syntax.n  in
                          match uu____3371 with
                          | FStar_Syntax_Syntax.Tm_arrow (dbs,c) ->
                              (debug_log env
                                 (fun uu____3400  ->
                                    "Checked nested positivity in Tm_arrow data constructor type");
                               (let uu____3402 =
                                  FStar_List.splitAt num_ibs dbs  in
                                match uu____3402 with
                                | (ibs,dbs1) ->
                                    let ibs1 =
                                      FStar_Syntax_Subst.open_binders ibs  in
                                    let dbs2 =
                                      let uu____3466 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____3466 dbs1
                                       in
                                    let c1 =
                                      let uu____3470 =
                                        FStar_Syntax_Subst.opening_of_binders
                                          ibs1
                                         in
                                      FStar_Syntax_Subst.subst_comp
                                        uu____3470 c
                                       in
                                    let uu____3473 =
                                      FStar_List.splitAt num_ibs args  in
                                    (match uu____3473 with
                                     | (args1,uu____3508) ->
                                         let subst =
                                           FStar_List.fold_left2
                                             (fun subst  ->
                                                fun ib  ->
                                                  fun arg  ->
                                                    FStar_List.append subst
                                                      [FStar_Syntax_Syntax.NT
                                                         ((FStar_Pervasives_Native.fst
                                                             ib),
                                                           (FStar_Pervasives_Native.fst
                                                              arg))]) [] ibs1
                                             args1
                                            in
                                         let dbs3 =
                                           FStar_Syntax_Subst.subst_binders
                                             subst dbs2
                                            in
                                         let c2 =
                                           let uu____3600 =
                                             FStar_Syntax_Subst.shift_subst
                                               (FStar_List.length dbs3) subst
                                              in
                                           FStar_Syntax_Subst.subst_comp
                                             uu____3600 c1
                                            in
                                         (debug_log env
                                            (fun uu____3612  ->
                                               let uu____3613 =
                                                 let uu____3615 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     "; " dbs3
                                                    in
                                                 let uu____3618 =
                                                   let uu____3620 =
                                                     FStar_Syntax_Print.comp_to_string
                                                       c2
                                                      in
                                                   Prims.op_Hat ", and c: "
                                                     uu____3620
                                                    in
                                                 Prims.op_Hat uu____3615
                                                   uu____3618
                                                  in
                                               Prims.op_Hat
                                                 "Checking nested positivity in the unfolded data constructor binders as: "
                                                 uu____3613);
                                          ty_nested_positive_in_type ty_lid
                                            (FStar_Syntax_Syntax.Tm_arrow
                                               (dbs3, c2)) ilid num_ibs
                                            unfolded env))))
                          | uu____3634 ->
                              (debug_log env
                                 (fun uu____3637  ->
                                    "Checking nested positivity in the data constructor type that is not an arrow");
                               (let uu____3639 =
                                  let uu____3640 =
                                    FStar_Syntax_Subst.compress dt1  in
                                  uu____3640.FStar_Syntax_Syntax.n  in
                                ty_nested_positive_in_type ty_lid uu____3639
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
                     (fun uu____3679  ->
                        "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
                   (let uu____3681 =
                      let uu____3686 = try_get_fv t1  in
                      FStar_All.pipe_right uu____3686 FStar_Util.must  in
                    match uu____3681 with
                    | (fv,uu____3709) ->
                        let uu____3710 =
                          FStar_Ident.lid_equals
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            ilid
                           in
                        if uu____3710
                        then true
                        else
                          failwith "Impossible, expected the type to be ilid"))
              | FStar_Syntax_Syntax.Tm_arrow (sbs,c) ->
                  (debug_log env
                     (fun uu____3744  ->
                        let uu____3745 =
                          FStar_Syntax_Print.binders_to_string "; " sbs  in
                        Prims.op_Hat
                          "Checking nested positivity in an Tm_arrow node, with binders as: "
                          uu____3745);
                   (let sbs1 = FStar_Syntax_Subst.open_binders sbs  in
                    let uu____3750 =
                      FStar_List.fold_left
                        (fun uu____3771  ->
                           fun b  ->
                             match uu____3771 with
                             | (r,env1) ->
                                 if Prims.op_Negation r
                                 then (r, env1)
                                 else
                                   (let uu____3802 =
                                      ty_strictly_positive_in_type ty_lid
                                        (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                        unfolded env1
                                       in
                                    let uu____3806 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        [b]
                                       in
                                    (uu____3802, uu____3806))) (true, env)
                        sbs1
                       in
                    match uu____3750 with | (b,uu____3824) -> b))
              | uu____3827 ->
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
              let uu____3863 = FStar_TypeChecker_Env.lookup_datacon env dlid
                 in
              match uu____3863 with
              | (univ_unif_vars,dt) ->
                  (FStar_List.iter2
                     (fun u'  ->
                        fun u  ->
                          match u' with
                          | FStar_Syntax_Syntax.U_unif u'' ->
                              FStar_Syntax_Unionfind.univ_change u'' u
                          | uu____3886 ->
                              failwith
                                "Impossible! Expected universe unification variables")
                     univ_unif_vars us;
                   debug_log env
                     (fun uu____3891  ->
                        let uu____3892 = FStar_Syntax_Print.term_to_string dt
                           in
                        Prims.op_Hat "Checking data constructor type: "
                          uu____3892);
                   (let uu____3895 =
                      let uu____3896 = FStar_Syntax_Subst.compress dt  in
                      uu____3896.FStar_Syntax_Syntax.n  in
                    match uu____3895 with
                    | FStar_Syntax_Syntax.Tm_fvar uu____3900 ->
                        (debug_log env
                           (fun uu____3903  ->
                              "Data constructor type is simply an fvar, returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____3907) ->
                        let dbs1 =
                          let uu____3937 =
                            FStar_List.splitAt (FStar_List.length ty_bs) dbs
                             in
                          FStar_Pervasives_Native.snd uu____3937  in
                        let dbs2 =
                          let uu____3987 =
                            FStar_Syntax_Subst.opening_of_binders ty_bs  in
                          FStar_Syntax_Subst.subst_binders uu____3987 dbs1
                           in
                        let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                        (debug_log env
                           (fun uu____3994  ->
                              let uu____3995 =
                                let uu____3997 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length dbs3)
                                   in
                                Prims.op_Hat uu____3997 " binders"  in
                              Prims.op_Hat
                                "Data constructor type is an arrow type, so checking strict positivity in "
                                uu____3995);
                         (let uu____4007 =
                            FStar_List.fold_left
                              (fun uu____4028  ->
                                 fun b  ->
                                   match uu____4028 with
                                   | (r,env1) ->
                                       if Prims.op_Negation r
                                       then (r, env1)
                                       else
                                         (let uu____4059 =
                                            ty_strictly_positive_in_type
                                              ty_lid
                                              (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                              unfolded env1
                                             in
                                          let uu____4063 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 [b]
                                             in
                                          (uu____4059, uu____4063)))
                              (true, env) dbs3
                             in
                          match uu____4007 with | (b,uu____4081) -> b))
                    | FStar_Syntax_Syntax.Tm_app (uu____4084,uu____4085) ->
                        (debug_log env
                           (fun uu____4112  ->
                              "Data constructor type is a Tm_app, so returning true");
                         true)
                    | FStar_Syntax_Syntax.Tm_uinst (t,univs) ->
                        (debug_log env
                           (fun uu____4123  ->
                              "Data constructor type is a Tm_uinst, so recursing in the base type");
                         ty_strictly_positive_in_type ty_lid t unfolded env)
                    | uu____4125 ->
                        failwith
                          "Unexpected data constructor type when checking positivity"))
  
let (check_positivity :
  FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env -> Prims.bool) =
  fun ty  ->
    fun env  ->
      let unfolded_inductives = FStar_Util.mk_ref []  in
      let uu____4148 =
        match ty.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid,us,bs,uu____4164,uu____4165,uu____4166) -> (lid, us, bs)
        | uu____4175 -> failwith "Impossible!"  in
      match uu____4148 with
      | (ty_lid,ty_us,ty_bs) ->
          let uu____4187 = FStar_Syntax_Subst.univ_var_opening ty_us  in
          (match uu____4187 with
           | (ty_usubst,ty_us1) ->
               let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1  in
               let env2 = FStar_TypeChecker_Env.push_binders env1 ty_bs  in
               let ty_bs1 = FStar_Syntax_Subst.subst_binders ty_usubst ty_bs
                  in
               let ty_bs2 = FStar_Syntax_Subst.open_binders ty_bs1  in
               let uu____4211 =
                 let uu____4214 =
                   FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid  in
                 FStar_Pervasives_Native.snd uu____4214  in
               FStar_List.for_all
                 (fun d  ->
                    let uu____4228 =
                      FStar_List.map (fun s  -> FStar_Syntax_Syntax.U_name s)
                        ty_us1
                       in
                    ty_positive_in_datacon ty_lid d ty_bs2 uu____4228
                      unfolded_inductives env2) uu____4211)
  
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
        (uu____4263,uu____4264,t,uu____4266,uu____4267,uu____4268) -> t
    | uu____4275 -> failwith "Impossible!"
  
let (haseq_suffix : Prims.string) = "__uu___haseq" 
let (is_haseq_lid : FStar_Ident.lid -> Prims.bool) =
  fun lid  ->
    let str = lid.FStar_Ident.str  in
    let len = FStar_String.length str  in
    let haseq_suffix_len = FStar_String.length haseq_suffix  in
    (len > haseq_suffix_len) &&
      (let uu____4292 =
         let uu____4294 =
           FStar_String.substring str (len - haseq_suffix_len)
             haseq_suffix_len
            in
         FStar_String.compare uu____4294 haseq_suffix  in
       uu____4292 = Prims.int_zero)
  
let (get_haseq_axiom_lid : FStar_Ident.lid -> FStar_Ident.lid) =
  fun lid  ->
    let uu____4304 =
      let uu____4307 =
        let uu____4310 =
          FStar_Ident.id_of_text
            (Prims.op_Hat (lid.FStar_Ident.ident).FStar_Ident.idText
               haseq_suffix)
           in
        [uu____4310]  in
      FStar_List.append lid.FStar_Ident.ns uu____4307  in
    FStar_Ident.lid_of_ids uu____4304
  
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
          let uu____4356 =
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,uu____4370,bs,t,uu____4373,uu____4374) -> (lid, bs, t)
            | uu____4383 -> failwith "Impossible!"  in
          match uu____4356 with
          | (lid,bs,t) ->
              let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
              let t1 =
                let uu____4406 =
                  FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                    usubst
                   in
                FStar_Syntax_Subst.subst uu____4406 t  in
              let uu____4415 = FStar_Syntax_Subst.open_term bs1 t1  in
              (match uu____4415 with
               | (bs2,t2) ->
                   let ibs =
                     let uu____4433 =
                       let uu____4434 = FStar_Syntax_Subst.compress t2  in
                       uu____4434.FStar_Syntax_Syntax.n  in
                     match uu____4433 with
                     | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____4438) -> ibs
                     | uu____4459 -> []  in
                   let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                   let ind =
                     let uu____4468 =
                       FStar_Syntax_Syntax.fvar lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let uu____4469 =
                       FStar_List.map
                         (fun u  -> FStar_Syntax_Syntax.U_name u) us
                        in
                     FStar_Syntax_Syntax.mk_Tm_uinst uu____4468 uu____4469
                      in
                   let ind1 =
                     let uu____4475 =
                       let uu____4480 =
                         FStar_List.map
                           (fun uu____4497  ->
                              match uu____4497 with
                              | (bv,aq) ->
                                  let uu____4516 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4516, aq)) bs2
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind uu____4480  in
                     uu____4475 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let ind2 =
                     let uu____4522 =
                       let uu____4527 =
                         FStar_List.map
                           (fun uu____4544  ->
                              match uu____4544 with
                              | (bv,aq) ->
                                  let uu____4563 =
                                    FStar_Syntax_Syntax.bv_to_name bv  in
                                  (uu____4563, aq)) ibs1
                          in
                       FStar_Syntax_Syntax.mk_Tm_app ind1 uu____4527  in
                     uu____4522 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let haseq_ind =
                     let uu____4569 =
                       let uu____4574 =
                         let uu____4575 = FStar_Syntax_Syntax.as_arg ind2  in
                         [uu____4575]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.t_haseq uu____4574
                        in
                     uu____4569 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange
                      in
                   let bs' =
                     FStar_List.filter
                       (fun b  ->
                          let uu____4624 =
                            let uu____4625 = FStar_Syntax_Util.type_u ()  in
                            FStar_Pervasives_Native.fst uu____4625  in
                          FStar_TypeChecker_Rel.subtype_nosmt_force en
                            (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            uu____4624) bs2
                      in
                   let haseq_bs =
                     FStar_List.fold_left
                       (fun t3  ->
                          fun b  ->
                            let uu____4638 =
                              let uu____4641 =
                                let uu____4646 =
                                  let uu____4647 =
                                    let uu____4656 =
                                      FStar_Syntax_Syntax.bv_to_name
                                        (FStar_Pervasives_Native.fst b)
                                       in
                                    FStar_Syntax_Syntax.as_arg uu____4656  in
                                  [uu____4647]  in
                                FStar_Syntax_Syntax.mk_Tm_app
                                  FStar_Syntax_Util.t_haseq uu____4646
                                 in
                              uu____4641 FStar_Pervasives_Native.None
                                FStar_Range.dummyRange
                               in
                            FStar_Syntax_Util.mk_conj t3 uu____4638)
                       FStar_Syntax_Util.t_true bs'
                      in
                   let fml = FStar_Syntax_Util.mk_imp haseq_bs haseq_ind  in
                   let fml1 =
                     let uu___676_4679 = fml  in
                     let uu____4680 =
                       let uu____4681 =
                         let uu____4688 =
                           let uu____4689 =
                             let uu____4710 =
                               FStar_Syntax_Syntax.binders_to_names ibs1  in
                             let uu____4715 =
                               let uu____4728 =
                                 let uu____4739 =
                                   FStar_Syntax_Syntax.as_arg haseq_ind  in
                                 [uu____4739]  in
                               [uu____4728]  in
                             (uu____4710, uu____4715)  in
                           FStar_Syntax_Syntax.Meta_pattern uu____4689  in
                         (fml, uu____4688)  in
                       FStar_Syntax_Syntax.Tm_meta uu____4681  in
                     {
                       FStar_Syntax_Syntax.n = uu____4680;
                       FStar_Syntax_Syntax.pos =
                         (uu___676_4679.FStar_Syntax_Syntax.pos);
                       FStar_Syntax_Syntax.vars =
                         (uu___676_4679.FStar_Syntax_Syntax.vars)
                     }  in
                   let fml2 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4808 =
                              let uu____4813 =
                                let uu____4814 =
                                  let uu____4823 =
                                    let uu____4824 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4824 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4823  in
                                [uu____4814]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4813
                               in
                            uu____4808 FStar_Pervasives_Native.None
                              FStar_Range.dummyRange) ibs1 fml1
                      in
                   let fml3 =
                     FStar_List.fold_right
                       (fun b  ->
                          fun t3  ->
                            let uu____4877 =
                              let uu____4882 =
                                let uu____4883 =
                                  let uu____4892 =
                                    let uu____4893 =
                                      FStar_Syntax_Subst.close [b] t3  in
                                    FStar_Syntax_Util.abs
                                      [((FStar_Pervasives_Native.fst b),
                                         FStar_Pervasives_Native.None)]
                                      uu____4893 FStar_Pervasives_Native.None
                                     in
                                  FStar_Syntax_Syntax.as_arg uu____4892  in
                                [uu____4883]  in
                              FStar_Syntax_Syntax.mk_Tm_app
                                FStar_Syntax_Util.tforall uu____4882
                               in
                            uu____4877 FStar_Pervasives_Native.None
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
          let uu____4968 =
            let uu____4969 = FStar_Syntax_Subst.compress dt1  in
            uu____4969.FStar_Syntax_Syntax.n  in
          match uu____4968 with
          | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____4973) ->
              let dbs1 =
                let uu____5003 =
                  FStar_List.splitAt (FStar_List.length bs) dbs  in
                FStar_Pervasives_Native.snd uu____5003  in
              let dbs2 =
                let uu____5053 = FStar_Syntax_Subst.opening_of_binders bs  in
                FStar_Syntax_Subst.subst_binders uu____5053 dbs1  in
              let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
              let cond =
                FStar_List.fold_left
                  (fun t  ->
                     fun b  ->
                       let haseq_b =
                         let uu____5068 =
                           let uu____5073 =
                             let uu____5074 =
                               FStar_Syntax_Syntax.as_arg
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                in
                             [uu____5074]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____5073
                            in
                         uu____5068 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let sort_range =
                         ((FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                          in
                       let haseq_b1 =
                         let uu____5105 =
                           FStar_Util.format1
                             "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier"
                             ty_lid.FStar_Ident.str
                            in
                         FStar_TypeChecker_Util.label uu____5105 sort_range
                           haseq_b
                          in
                       FStar_Syntax_Util.mk_conj t haseq_b1)
                  FStar_Syntax_Util.t_true dbs3
                 in
              FStar_List.fold_right
                (fun b  ->
                   fun t  ->
                     let uu____5113 =
                       let uu____5118 =
                         let uu____5119 =
                           let uu____5128 =
                             let uu____5129 = FStar_Syntax_Subst.close [b] t
                                in
                             FStar_Syntax_Util.abs
                               [((FStar_Pervasives_Native.fst b),
                                  FStar_Pervasives_Native.None)] uu____5129
                               FStar_Pervasives_Native.None
                              in
                           FStar_Syntax_Syntax.as_arg uu____5128  in
                         [uu____5119]  in
                       FStar_Syntax_Syntax.mk_Tm_app
                         FStar_Syntax_Util.tforall uu____5118
                        in
                     uu____5113 FStar_Pervasives_Native.None
                       FStar_Range.dummyRange) dbs3 cond
          | uu____5176 -> FStar_Syntax_Util.t_true
  
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
                  (lid,uu____5267,uu____5268,uu____5269,uu____5270,uu____5271)
                  -> lid
              | uu____5280 -> failwith "Impossible!"  in
            let uu____5282 = acc  in
            match uu____5282 with
            | (uu____5319,en,uu____5321,uu____5322) ->
                let uu____5343 = get_optimized_haseq_axiom en ty usubst us
                   in
                (match uu____5343 with
                 | (axiom_lid,fml,bs,ibs,haseq_bs) ->
                     let guard = FStar_Syntax_Util.mk_conj haseq_bs fml  in
                     let uu____5380 = acc  in
                     (match uu____5380 with
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
                                     (uu____5455,uu____5456,uu____5457,t_lid,uu____5459,uu____5460)
                                     -> t_lid = lid
                                 | uu____5467 -> failwith "Impossible")
                              all_datas_in_the_bundle
                             in
                          let cond =
                            FStar_List.fold_left
                              (fun acc1  ->
                                 fun d  ->
                                   let uu____5482 =
                                     optimized_haseq_soundness_for_data lid d
                                       usubst bs
                                      in
                                   FStar_Syntax_Util.mk_conj acc1 uu____5482)
                              FStar_Syntax_Util.t_true t_datas
                             in
                          let uu____5485 =
                            FStar_Syntax_Util.mk_conj guard' guard  in
                          let uu____5488 =
                            FStar_Syntax_Util.mk_conj cond' cond  in
                          ((FStar_List.append l_axioms [(axiom_lid, fml)]),
                            env2, uu____5485, uu____5488)))
  
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
          let uu____5546 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5556,us,uu____5558,t,uu____5560,uu____5561) -> 
                (us, t)
            | uu____5570 -> failwith "Impossible!"  in
          match uu____5546 with
          | (us,t) ->
              let uu____5580 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____5580 with
               | (usubst,us1) ->
                   let env = FStar_TypeChecker_Env.push_sigelt env0 sig_bndle
                      in
                   ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push
                      "haseq";
                    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                      env sig_bndle;
                    (let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     let uu____5606 =
                       FStar_List.fold_left
                         (optimized_haseq_ty datas usubst us1)
                         ([], env1, FStar_Syntax_Util.t_true,
                           FStar_Syntax_Util.t_true) tcs
                        in
                     match uu____5606 with
                     | (axioms,env2,guard,cond) ->
                         let phi =
                           let uu____5684 = FStar_Syntax_Util.arrow_formals t
                              in
                           match uu____5684 with
                           | (uu____5691,t1) ->
                               let uu____5697 =
                                 FStar_Syntax_Util.is_eqtype_no_unrefine t1
                                  in
                               if uu____5697
                               then cond
                               else FStar_Syntax_Util.mk_imp guard cond
                            in
                         let uu____5702 =
                           FStar_TypeChecker_TcTerm.tc_trivial_guard env2 phi
                            in
                         (match uu____5702 with
                          | (phi1,uu____5710) ->
                              ((let uu____5712 =
                                  FStar_TypeChecker_Env.should_verify env2
                                   in
                                if uu____5712
                                then
                                  let uu____5715 =
                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                      (FStar_TypeChecker_Common.NonTrivial
                                         phi1)
                                     in
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env2 uu____5715
                                else ());
                               (let ses =
                                  FStar_List.fold_left
                                    (fun l  ->
                                       fun uu____5733  ->
                                         match uu____5733 with
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
                let uu____5805 =
                  let uu____5806 = FStar_Syntax_Subst.compress t  in
                  uu____5806.FStar_Syntax_Syntax.n  in
                match uu____5805 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_List.existsb
                      (fun lid  ->
                         FStar_Ident.lid_equals lid
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                      mutuals
                | FStar_Syntax_Syntax.Tm_uinst (t',uu____5814) ->
                    is_mutual t'
                | FStar_Syntax_Syntax.Tm_refine (bv,t') ->
                    is_mutual bv.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_app (t',args) ->
                    let uu____5851 = is_mutual t'  in
                    if uu____5851
                    then true
                    else
                      (let uu____5858 =
                         FStar_List.map FStar_Pervasives_Native.fst args  in
                       exists_mutual uu____5858)
                | FStar_Syntax_Syntax.Tm_meta (t',uu____5878) -> is_mutual t'
                | uu____5883 -> false
              
              and exists_mutual uu___1_5885 =
                match uu___1_5885 with
                | [] -> false
                | hd::tl -> (is_mutual hd) || (exists_mutual tl)
               in
              let dt = datacon_typ data  in
              let dt1 = FStar_Syntax_Subst.subst usubst dt  in
              let uu____5906 =
                let uu____5907 = FStar_Syntax_Subst.compress dt1  in
                uu____5907.FStar_Syntax_Syntax.n  in
              match uu____5906 with
              | FStar_Syntax_Syntax.Tm_arrow (dbs,uu____5913) ->
                  let dbs1 =
                    let uu____5943 =
                      FStar_List.splitAt (FStar_List.length bs) dbs  in
                    FStar_Pervasives_Native.snd uu____5943  in
                  let dbs2 =
                    let uu____5993 = FStar_Syntax_Subst.opening_of_binders bs
                       in
                    FStar_Syntax_Subst.subst_binders uu____5993 dbs1  in
                  let dbs3 = FStar_Syntax_Subst.open_binders dbs2  in
                  let cond =
                    FStar_List.fold_left
                      (fun t  ->
                         fun b  ->
                           let sort =
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let haseq_sort =
                             let uu____6013 =
                               let uu____6018 =
                                 let uu____6019 =
                                   FStar_Syntax_Syntax.as_arg
                                     (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                    in
                                 [uu____6019]  in
                               FStar_Syntax_Syntax.mk_Tm_app
                                 FStar_Syntax_Util.t_haseq uu____6018
                                in
                             uu____6013 FStar_Pervasives_Native.None
                               FStar_Range.dummyRange
                              in
                           let haseq_sort1 =
                             let uu____6049 = is_mutual sort  in
                             if uu____6049
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
                           let uu____6062 =
                             let uu____6067 =
                               let uu____6068 =
                                 let uu____6077 =
                                   let uu____6078 =
                                     FStar_Syntax_Subst.close [b] t  in
                                   FStar_Syntax_Util.abs
                                     [((FStar_Pervasives_Native.fst b),
                                        FStar_Pervasives_Native.None)]
                                     uu____6078 FStar_Pervasives_Native.None
                                    in
                                 FStar_Syntax_Syntax.as_arg uu____6077  in
                               [uu____6068]  in
                             FStar_Syntax_Syntax.mk_Tm_app
                               FStar_Syntax_Util.tforall uu____6067
                              in
                           uu____6062 FStar_Pervasives_Native.None
                             FStar_Range.dummyRange) dbs3 cond
                     in
                  FStar_Syntax_Util.mk_conj acc cond1
              | uu____6125 -> acc
  
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
              let uu____6175 =
                match ty.FStar_Syntax_Syntax.sigel with
                | FStar_Syntax_Syntax.Sig_inductive_typ
                    (lid,uu____6197,bs,t,uu____6200,d_lids) ->
                    (lid, bs, t, d_lids)
                | uu____6212 -> failwith "Impossible!"  in
              match uu____6175 with
              | (lid,bs,t,d_lids) ->
                  let bs1 = FStar_Syntax_Subst.subst_binders usubst bs  in
                  let t1 =
                    let uu____6236 =
                      FStar_Syntax_Subst.shift_subst (FStar_List.length bs1)
                        usubst
                       in
                    FStar_Syntax_Subst.subst uu____6236 t  in
                  let uu____6245 = FStar_Syntax_Subst.open_term bs1 t1  in
                  (match uu____6245 with
                   | (bs2,t2) ->
                       let ibs =
                         let uu____6255 =
                           let uu____6256 = FStar_Syntax_Subst.compress t2
                              in
                           uu____6256.FStar_Syntax_Syntax.n  in
                         match uu____6255 with
                         | FStar_Syntax_Syntax.Tm_arrow (ibs,uu____6260) ->
                             ibs
                         | uu____6281 -> []  in
                       let ibs1 = FStar_Syntax_Subst.open_binders ibs  in
                       let ind =
                         let uu____6290 =
                           FStar_Syntax_Syntax.fvar lid
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None
                            in
                         let uu____6291 =
                           FStar_List.map
                             (fun u  -> FStar_Syntax_Syntax.U_name u) us
                            in
                         FStar_Syntax_Syntax.mk_Tm_uinst uu____6290
                           uu____6291
                          in
                       let ind1 =
                         let uu____6297 =
                           let uu____6302 =
                             FStar_List.map
                               (fun uu____6319  ->
                                  match uu____6319 with
                                  | (bv,aq) ->
                                      let uu____6338 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6338, aq)) bs2
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind uu____6302  in
                         uu____6297 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let ind2 =
                         let uu____6344 =
                           let uu____6349 =
                             FStar_List.map
                               (fun uu____6366  ->
                                  match uu____6366 with
                                  | (bv,aq) ->
                                      let uu____6385 =
                                        FStar_Syntax_Syntax.bv_to_name bv  in
                                      (uu____6385, aq)) ibs1
                              in
                           FStar_Syntax_Syntax.mk_Tm_app ind1 uu____6349  in
                         uu____6344 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let haseq_ind =
                         let uu____6391 =
                           let uu____6396 =
                             let uu____6397 = FStar_Syntax_Syntax.as_arg ind2
                                in
                             [uu____6397]  in
                           FStar_Syntax_Syntax.mk_Tm_app
                             FStar_Syntax_Util.t_haseq uu____6396
                            in
                         uu____6391 FStar_Pervasives_Native.None
                           FStar_Range.dummyRange
                          in
                       let t_datas =
                         FStar_List.filter
                           (fun s  ->
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_datacon
                                  (uu____6434,uu____6435,uu____6436,t_lid,uu____6438,uu____6439)
                                  -> t_lid = lid
                              | uu____6446 -> failwith "Impossible")
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
                         let uu___913_6458 = fml  in
                         let uu____6459 =
                           let uu____6460 =
                             let uu____6467 =
                               let uu____6468 =
                                 let uu____6489 =
                                   FStar_Syntax_Syntax.binders_to_names ibs1
                                    in
                                 let uu____6494 =
                                   let uu____6507 =
                                     let uu____6518 =
                                       FStar_Syntax_Syntax.as_arg haseq_ind
                                        in
                                     [uu____6518]  in
                                   [uu____6507]  in
                                 (uu____6489, uu____6494)  in
                               FStar_Syntax_Syntax.Meta_pattern uu____6468
                                in
                             (fml, uu____6467)  in
                           FStar_Syntax_Syntax.Tm_meta uu____6460  in
                         {
                           FStar_Syntax_Syntax.n = uu____6459;
                           FStar_Syntax_Syntax.pos =
                             (uu___913_6458.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___913_6458.FStar_Syntax_Syntax.vars)
                         }  in
                       let fml2 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6587 =
                                  let uu____6592 =
                                    let uu____6593 =
                                      let uu____6602 =
                                        let uu____6603 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6603
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6602
                                       in
                                    [uu____6593]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6592
                                   in
                                uu____6587 FStar_Pervasives_Native.None
                                  FStar_Range.dummyRange) ibs1 fml1
                          in
                       let fml3 =
                         FStar_List.fold_right
                           (fun b  ->
                              fun t3  ->
                                let uu____6656 =
                                  let uu____6661 =
                                    let uu____6662 =
                                      let uu____6671 =
                                        let uu____6672 =
                                          FStar_Syntax_Subst.close [b] t3  in
                                        FStar_Syntax_Util.abs
                                          [((FStar_Pervasives_Native.fst b),
                                             FStar_Pervasives_Native.None)]
                                          uu____6672
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.as_arg uu____6671
                                       in
                                    [uu____6662]  in
                                  FStar_Syntax_Syntax.mk_Tm_app
                                    FStar_Syntax_Util.tforall uu____6661
                                   in
                                uu____6656 FStar_Pervasives_Native.None
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
                     (lid,uu____6764,uu____6765,uu____6766,uu____6767,uu____6768)
                     -> lid
                 | uu____6777 -> failwith "Impossible!") tcs
             in
          let uu____6779 =
            let ty = FStar_List.hd tcs  in
            match ty.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_inductive_typ
                (lid,us,uu____6791,uu____6792,uu____6793,uu____6794) ->
                (lid, us)
            | uu____6803 -> failwith "Impossible!"  in
          match uu____6779 with
          | (lid,us) ->
              let uu____6813 = FStar_Syntax_Subst.univ_var_opening us  in
              (match uu____6813 with
               | (usubst,us1) ->
                   let fml =
                     FStar_List.fold_left
                       (unoptimized_haseq_ty datas mutuals usubst us1)
                       FStar_Syntax_Util.t_true tcs
                      in
                   let se =
                     let uu____6840 =
                       let uu____6841 =
                         let uu____6848 = get_haseq_axiom_lid lid  in
                         (uu____6848, us1, fml)  in
                       FStar_Syntax_Syntax.Sig_assume uu____6841  in
                     {
                       FStar_Syntax_Syntax.sigel = uu____6840;
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
          let uu____6902 =
            FStar_All.pipe_right ses
              (FStar_List.partition
                 (fun uu___2_6928  ->
                    match uu___2_6928 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_inductive_typ uu____6930;
                        FStar_Syntax_Syntax.sigrng = uu____6931;
                        FStar_Syntax_Syntax.sigquals = uu____6932;
                        FStar_Syntax_Syntax.sigmeta = uu____6933;
                        FStar_Syntax_Syntax.sigattrs = uu____6934;
                        FStar_Syntax_Syntax.sigopts = uu____6935;_} -> true
                    | uu____6959 -> false))
             in
          match uu____6902 with
          | (tys,datas) ->
              ((let uu____6982 =
                  FStar_All.pipe_right datas
                    (FStar_Util.for_some
                       (fun uu___3_6994  ->
                          match uu___3_6994 with
                          | {
                              FStar_Syntax_Syntax.sigel =
                                FStar_Syntax_Syntax.Sig_datacon uu____6996;
                              FStar_Syntax_Syntax.sigrng = uu____6997;
                              FStar_Syntax_Syntax.sigquals = uu____6998;
                              FStar_Syntax_Syntax.sigmeta = uu____6999;
                              FStar_Syntax_Syntax.sigattrs = uu____7000;
                              FStar_Syntax_Syntax.sigopts = uu____7001;_} ->
                              false
                          | uu____7024 -> true))
                   in
                if uu____6982
                then
                  let uu____7027 = FStar_TypeChecker_Env.get_range env  in
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                      "Mutually defined type contains a non-inductive element")
                    uu____7027
                else ());
               (let univs =
                  if (FStar_List.length tys) = Prims.int_zero
                  then []
                  else
                    (let uu____7042 =
                       let uu____7043 = FStar_List.hd tys  in
                       uu____7043.FStar_Syntax_Syntax.sigel  in
                     match uu____7042 with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (uu____7046,uvs,uu____7048,uu____7049,uu____7050,uu____7051)
                         -> uvs
                     | uu____7060 -> failwith "Impossible, can't happen!")
                   in
                let env0 = env  in
                let uu____7065 =
                  FStar_List.fold_right
                    (fun tc  ->
                       fun uu____7104  ->
                         match uu____7104 with
                         | (env1,all_tcs,g) ->
                             let uu____7144 = tc_tycon env1 tc  in
                             (match uu____7144 with
                              | (env2,tc1,tc_u,guard) ->
                                  let g' =
                                    FStar_TypeChecker_Rel.universe_inequality
                                      FStar_Syntax_Syntax.U_zero tc_u
                                     in
                                  ((let uu____7171 =
                                      FStar_TypeChecker_Env.debug env2
                                        FStar_Options.Low
                                       in
                                    if uu____7171
                                    then
                                      let uu____7174 =
                                        FStar_Syntax_Print.sigelt_to_string
                                          tc1
                                         in
                                      FStar_Util.print1
                                        "Checked inductive: %s\n" uu____7174
                                    else ());
                                   (let uu____7179 =
                                      let uu____7180 =
                                        FStar_TypeChecker_Env.conj_guard
                                          guard g'
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____7180
                                       in
                                    (env2, ((tc1, tc_u) :: all_tcs),
                                      uu____7179))))) tys
                    (env, [], FStar_TypeChecker_Env.trivial_guard)
                   in
                match uu____7065 with
                | (env1,tcs,g) ->
                    let uu____7226 =
                      FStar_List.fold_right
                        (fun se  ->
                           fun uu____7248  ->
                             match uu____7248 with
                             | (datas1,g1) ->
                                 let uu____7267 =
                                   let uu____7272 = tc_data env1 tcs  in
                                   uu____7272 se  in
                                 (match uu____7267 with
                                  | (data,g') ->
                                      let uu____7289 =
                                        FStar_TypeChecker_Env.conj_guard g1
                                          g'
                                         in
                                      ((data :: datas1), uu____7289))) datas
                        ([], g)
                       in
                    (match uu____7226 with
                     | (datas1,g1) ->
                         let uu____7310 =
                           let tc_universe_vars =
                             FStar_List.map FStar_Pervasives_Native.snd tcs
                              in
                           let g2 =
                             let uu___1024_7327 = g1  in
                             {
                               FStar_TypeChecker_Common.guard_f =
                                 (uu___1024_7327.FStar_TypeChecker_Common.guard_f);
                               FStar_TypeChecker_Common.deferred =
                                 (uu___1024_7327.FStar_TypeChecker_Common.deferred);
                               FStar_TypeChecker_Common.univ_ineqs =
                                 (tc_universe_vars,
                                   (FStar_Pervasives_Native.snd
                                      g1.FStar_TypeChecker_Common.univ_ineqs));
                               FStar_TypeChecker_Common.implicits =
                                 (uu___1024_7327.FStar_TypeChecker_Common.implicits)
                             }  in
                           (let uu____7337 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "GenUniverses")
                               in
                            if uu____7337
                            then
                              let uu____7342 =
                                FStar_TypeChecker_Rel.guard_to_string env1 g2
                                 in
                              FStar_Util.print1
                                "@@@@@@Guard before (possible) generalization: %s\n"
                                uu____7342
                            else ());
                           FStar_TypeChecker_Rel.force_trivial_guard env0 g2;
                           if (FStar_List.length univs) = Prims.int_zero
                           then generalize_and_inst_within env0 tcs datas1
                           else
                             (let uu____7361 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  tcs
                                 in
                              (uu____7361, datas1))
                            in
                         (match uu____7310 with
                          | (tcs1,datas2) ->
                              let sig_bndle =
                                let uu____7393 =
                                  FStar_TypeChecker_Env.get_range env0  in
                                let uu____7394 =
                                  FStar_List.collect
                                    (fun s  -> s.FStar_Syntax_Syntax.sigattrs)
                                    ses
                                   in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_bundle
                                       ((FStar_List.append tcs1 datas2),
                                         lids));
                                  FStar_Syntax_Syntax.sigrng = uu____7393;
                                  FStar_Syntax_Syntax.sigquals = quals;
                                  FStar_Syntax_Syntax.sigmeta =
                                    FStar_Syntax_Syntax.default_sigmeta;
                                  FStar_Syntax_Syntax.sigattrs = uu____7394;
                                  FStar_Syntax_Syntax.sigopts =
                                    FStar_Pervasives_Native.None
                                }  in
                              (FStar_All.pipe_right tcs1
                                 (FStar_List.iter
                                    (fun se  ->
                                       match se.FStar_Syntax_Syntax.sigel
                                       with
                                       | FStar_Syntax_Syntax.Sig_inductive_typ
                                           (l,univs1,binders,typ,uu____7420,uu____7421)
                                           ->
                                           let fail expected inferred =
                                             let uu____7441 =
                                               let uu____7447 =
                                                 let uu____7449 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     expected
                                                    in
                                                 let uu____7451 =
                                                   FStar_Syntax_Print.tscheme_to_string
                                                     inferred
                                                    in
                                                 FStar_Util.format2
                                                   "Expected an inductive with type %s; got %s"
                                                   uu____7449 uu____7451
                                                  in
                                               (FStar_Errors.Fatal_UnexpectedInductivetype,
                                                 uu____7447)
                                                in
                                             FStar_Errors.raise_error
                                               uu____7441
                                               se.FStar_Syntax_Syntax.sigrng
                                              in
                                           let uu____7455 =
                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                               env0 l
                                              in
                                           (match uu____7455 with
                                            | FStar_Pervasives_Native.None 
                                                -> ()
                                            | FStar_Pervasives_Native.Some
                                                (expected_typ,uu____7471) ->
                                                let inferred_typ =
                                                  let body =
                                                    match binders with
                                                    | [] -> typ
                                                    | uu____7502 ->
                                                        let uu____7503 =
                                                          let uu____7510 =
                                                            let uu____7511 =
                                                              let uu____7526
                                                                =
                                                                FStar_Syntax_Syntax.mk_Total
                                                                  typ
                                                                 in
                                                              (binders,
                                                                uu____7526)
                                                               in
                                                            FStar_Syntax_Syntax.Tm_arrow
                                                              uu____7511
                                                             in
                                                          FStar_Syntax_Syntax.mk
                                                            uu____7510
                                                           in
                                                        uu____7503
                                                          FStar_Pervasives_Native.None
                                                          se.FStar_Syntax_Syntax.sigrng
                                                     in
                                                  (univs1, body)  in
                                                if
                                                  (FStar_List.length univs1)
                                                    =
                                                    (FStar_List.length
                                                       (FStar_Pervasives_Native.fst
                                                          expected_typ))
                                                then
                                                  let uu____7548 =
                                                    FStar_TypeChecker_Env.inst_tscheme
                                                      inferred_typ
                                                     in
                                                  (match uu____7548 with
                                                   | (uu____7553,inferred) ->
                                                       let uu____7555 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           expected_typ
                                                          in
                                                       (match uu____7555 with
                                                        | (uu____7560,expected)
                                                            ->
                                                            let uu____7562 =
                                                              FStar_TypeChecker_Rel.teq_nosmt_force
                                                                env0 inferred
                                                                expected
                                                               in
                                                            if uu____7562
                                                            then ()
                                                            else
                                                              fail
                                                                expected_typ
                                                                inferred_typ))
                                                else
                                                  fail expected_typ
                                                    inferred_typ)
                                       | uu____7569 -> ()));
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
                        fun erasable  ->
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
                              let uu____7696 =
                                let uu____7703 =
                                  let uu____7704 =
                                    let uu____7711 =
                                      let uu____7714 =
                                        FStar_Syntax_Syntax.lid_as_fv tc
                                          FStar_Syntax_Syntax.delta_constant
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Syntax_Syntax.fv_to_tm uu____7714
                                       in
                                    (uu____7711, inst_univs)  in
                                  FStar_Syntax_Syntax.Tm_uinst uu____7704  in
                                FStar_Syntax_Syntax.mk uu____7703  in
                              uu____7696 FStar_Pervasives_Native.None p  in
                            let args =
                              FStar_All.pipe_right
                                (FStar_List.append tps indices)
                                (FStar_List.map
                                   (fun uu____7748  ->
                                      match uu____7748 with
                                      | (x,imp) ->
                                          let uu____7767 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7767, imp)))
                               in
                            FStar_Syntax_Syntax.mk_Tm_app inst_tc args
                              FStar_Pervasives_Native.None p
                             in
                          let unrefined_arg_binder =
                            let uu____7771 = projectee arg_typ  in
                            FStar_Syntax_Syntax.mk_binder uu____7771  in
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
                                   let uu____7794 =
                                     FStar_Ident.set_lid_range disc_name p
                                      in
                                   FStar_Syntax_Syntax.fvar uu____7794
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                     FStar_Pervasives_Native.None
                                    in
                                 let uu____7796 =
                                   let uu____7799 =
                                     let uu____7802 =
                                       let uu____7807 =
                                         FStar_Syntax_Syntax.mk_Tm_uinst
                                           disc_fvar inst_univs
                                          in
                                       let uu____7808 =
                                         let uu____7809 =
                                           let uu____7818 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             uu____7818
                                            in
                                         [uu____7809]  in
                                       FStar_Syntax_Syntax.mk_Tm_app
                                         uu____7807 uu____7808
                                        in
                                     uu____7802 FStar_Pervasives_Native.None
                                       p
                                      in
                                   FStar_Syntax_Util.b2t uu____7799  in
                                 FStar_Syntax_Util.refine x uu____7796  in
                               let uu____7843 =
                                 let uu___1099_7844 = projectee arg_typ  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1099_7844.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1099_7844.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = sort
                                 }  in
                               FStar_Syntax_Syntax.mk_binder uu____7843)
                             in
                          let ntps = FStar_List.length tps  in
                          let all_params =
                            let uu____7861 =
                              FStar_List.map
                                (fun uu____7885  ->
                                   match uu____7885 with
                                   | (x,uu____7899) ->
                                       (x,
                                         (FStar_Pervasives_Native.Some
                                            FStar_Syntax_Syntax.imp_tag)))
                                tps
                               in
                            FStar_List.append uu____7861 fields  in
                          let imp_binders =
                            FStar_All.pipe_right
                              (FStar_List.append tps indices)
                              (FStar_List.map
                                 (fun uu____7958  ->
                                    match uu____7958 with
                                    | (x,uu____7972) ->
                                        (x,
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.imp_tag))))
                             in
                          let early_prims_inductive =
                            (let uu____7983 =
                               FStar_TypeChecker_Env.current_module env  in
                             FStar_Ident.lid_equals
                               FStar_Parser_Const.prims_lid uu____7983)
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
                                   (let uu____8004 =
                                      let uu____8006 =
                                        FStar_TypeChecker_Env.current_module
                                          env
                                         in
                                      uu____8006.FStar_Ident.str  in
                                    FStar_Options.dont_gen_projectors
                                      uu____8004)
                                  in
                               let quals =
                                 let uu____8010 =
                                   FStar_List.filter
                                     (fun uu___4_8014  ->
                                        match uu___4_8014 with
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            Prims.op_Negation only_decl
                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                             -> true
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____8019 -> false) iquals
                                    in
                                 FStar_List.append
                                   ((FStar_Syntax_Syntax.Discriminator lid)
                                   ::
                                   (if only_decl
                                    then
                                      [FStar_Syntax_Syntax.Logic;
                                      FStar_Syntax_Syntax.Assumption]
                                    else [])) uu____8010
                                  in
                               let binders =
                                 FStar_List.append imp_binders
                                   [unrefined_arg_binder]
                                  in
                               let t =
                                 let bool_typ =
                                   if erasable
                                   then
                                     FStar_Syntax_Syntax.mk_GTotal
                                       FStar_Syntax_Util.t_bool
                                   else
                                     FStar_Syntax_Syntax.mk_Total
                                       FStar_Syntax_Util.t_bool
                                    in
                                 let uu____8064 =
                                   FStar_Syntax_Util.arrow binders bool_typ
                                    in
                                 FStar_All.pipe_left
                                   (FStar_Syntax_Subst.close_univ_vars uvs)
                                   uu____8064
                                  in
                               let decl =
                                 let uu____8068 =
                                   FStar_Ident.range_of_lid
                                     discriminator_name
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_declare_typ
                                        (discriminator_name, uvs, t));
                                   FStar_Syntax_Syntax.sigrng = uu____8068;
                                   FStar_Syntax_Syntax.sigquals = quals;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = attrs;
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               (let uu____8070 =
                                  FStar_TypeChecker_Env.debug env
                                    (FStar_Options.Other "LogTypes")
                                   in
                                if uu____8070
                                then
                                  let uu____8074 =
                                    FStar_Syntax_Print.sigelt_to_string decl
                                     in
                                  FStar_Util.print1
                                    "Declaration of a discriminator %s\n"
                                    uu____8074
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
                                                 fun uu____8135  ->
                                                   match uu____8135 with
                                                   | (x,imp) ->
                                                       let b =
                                                         FStar_Syntax_Syntax.is_implicit
                                                           imp
                                                          in
                                                       if b && (j < ntps)
                                                       then
                                                         let uu____8160 =
                                                           let uu____8163 =
                                                             let uu____8164 =
                                                               let uu____8171
                                                                 =
                                                                 FStar_Syntax_Syntax.gen_bv
                                                                   (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                   FStar_Pervasives_Native.None
                                                                   FStar_Syntax_Syntax.tun
                                                                  in
                                                               (uu____8171,
                                                                 FStar_Syntax_Syntax.tun)
                                                                in
                                                             FStar_Syntax_Syntax.Pat_dot_term
                                                               uu____8164
                                                              in
                                                           pos uu____8163  in
                                                         (uu____8160, b)
                                                       else
                                                         (let uu____8179 =
                                                            let uu____8182 =
                                                              let uu____8183
                                                                =
                                                                FStar_Syntax_Syntax.gen_bv
                                                                  (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                  FStar_Pervasives_Native.None
                                                                  FStar_Syntax_Syntax.tun
                                                                 in
                                                              FStar_Syntax_Syntax.Pat_wild
                                                                uu____8183
                                                               in
                                                            pos uu____8182
                                                             in
                                                          (uu____8179, b))))
                                          in
                                       let pat_true =
                                         let uu____8202 =
                                           let uu____8205 =
                                             let uu____8206 =
                                               let uu____8220 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   (FStar_Pervasives_Native.Some
                                                      fvq)
                                                  in
                                               (uu____8220, arg_pats)  in
                                             FStar_Syntax_Syntax.Pat_cons
                                               uu____8206
                                              in
                                           pos uu____8205  in
                                         (uu____8202,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_true_bool)
                                          in
                                       let pat_false =
                                         let uu____8255 =
                                           let uu____8258 =
                                             let uu____8259 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Syntax.tun
                                                in
                                             FStar_Syntax_Syntax.Pat_wild
                                               uu____8259
                                              in
                                           pos uu____8258  in
                                         (uu____8255,
                                           FStar_Pervasives_Native.None,
                                           FStar_Syntax_Util.exp_false_bool)
                                          in
                                       let arg_exp =
                                         FStar_Syntax_Syntax.bv_to_name
                                           (FStar_Pervasives_Native.fst
                                              unrefined_arg_binder)
                                          in
                                       let uu____8273 =
                                         let uu____8280 =
                                           let uu____8281 =
                                             let uu____8304 =
                                               let uu____8321 =
                                                 FStar_Syntax_Util.branch
                                                   pat_true
                                                  in
                                               let uu____8336 =
                                                 let uu____8353 =
                                                   FStar_Syntax_Util.branch
                                                     pat_false
                                                    in
                                                 [uu____8353]  in
                                               uu____8321 :: uu____8336  in
                                             (arg_exp, uu____8304)  in
                                           FStar_Syntax_Syntax.Tm_match
                                             uu____8281
                                            in
                                         FStar_Syntax_Syntax.mk uu____8280
                                          in
                                       uu____8273
                                         FStar_Pervasives_Native.None p)
                                     in
                                  let dd =
                                    let uu____8429 =
                                      FStar_All.pipe_right quals
                                        (FStar_List.contains
                                           FStar_Syntax_Syntax.Abstract)
                                       in
                                    if uu____8429
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
                                    let uu____8451 =
                                      let uu____8456 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          discriminator_name dd
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_Util.Inr uu____8456  in
                                    let uu____8457 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        imp
                                       in
                                    FStar_Syntax_Util.mk_letbinding
                                      uu____8451 uvs lbtyp
                                      FStar_Parser_Const.effect_Tot_lid
                                      uu____8457 [] FStar_Range.dummyRange
                                     in
                                  let impl =
                                    let uu____8463 =
                                      let uu____8464 =
                                        let uu____8471 =
                                          let uu____8474 =
                                            let uu____8475 =
                                              FStar_All.pipe_right
                                                lb.FStar_Syntax_Syntax.lbname
                                                FStar_Util.right
                                               in
                                            FStar_All.pipe_right uu____8475
                                              (fun fv  ->
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                             in
                                          [uu____8474]  in
                                        ((false, [lb]), uu____8471)  in
                                      FStar_Syntax_Syntax.Sig_let uu____8464
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____8463;
                                      FStar_Syntax_Syntax.sigrng = p;
                                      FStar_Syntax_Syntax.sigquals = quals;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = attrs;
                                      FStar_Syntax_Syntax.sigopts =
                                        FStar_Pervasives_Native.None
                                    }  in
                                  (let uu____8489 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "LogTypes")
                                      in
                                   if uu____8489
                                   then
                                     let uu____8493 =
                                       FStar_Syntax_Print.sigelt_to_string
                                         impl
                                        in
                                     FStar_Util.print1
                                       "Implementation of a discriminator %s\n"
                                       uu____8493
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
                          let subst =
                            FStar_All.pipe_right fields
                              (FStar_List.mapi
                                 (fun i  ->
                                    fun uu____8564  ->
                                      match uu____8564 with
                                      | (a,uu____8573) ->
                                          let field_name =
                                            FStar_Syntax_Util.mk_field_projector_name
                                              lid a i
                                             in
                                          let field_proj_tm =
                                            let uu____8580 =
                                              let uu____8581 =
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  field_name
                                                  (FStar_Syntax_Syntax.Delta_equational_at_level
                                                     Prims.int_one)
                                                  FStar_Pervasives_Native.None
                                                 in
                                              FStar_Syntax_Syntax.fv_to_tm
                                                uu____8581
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              uu____8580 inst_univs
                                             in
                                          let proj =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              field_proj_tm [arg]
                                              FStar_Pervasives_Native.None p
                                             in
                                          FStar_Syntax_Syntax.NT (a, proj)))
                             in
                          let projectors_ses =
                            let uu____8607 =
                              FStar_All.pipe_right fields
                                (FStar_List.mapi
                                   (fun i  ->
                                      fun uu____8647  ->
                                        match uu____8647 with
                                        | (x,uu____8658) ->
                                            let p1 =
                                              FStar_Syntax_Syntax.range_of_bv
                                                x
                                               in
                                            let field_name =
                                              FStar_Syntax_Util.mk_field_projector_name
                                                lid x i
                                               in
                                            let t =
                                              let result_comp =
                                                let t =
                                                  FStar_Syntax_Subst.subst
                                                    subst
                                                    x.FStar_Syntax_Syntax.sort
                                                   in
                                                if erasable
                                                then
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                else
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t
                                                 in
                                              let uu____8677 =
                                                FStar_Syntax_Util.arrow
                                                  binders result_comp
                                                 in
                                              FStar_All.pipe_left
                                                (FStar_Syntax_Subst.close_univ_vars
                                                   uvs) uu____8677
                                               in
                                            let only_decl =
                                              early_prims_inductive ||
                                                (let uu____8683 =
                                                   let uu____8685 =
                                                     FStar_TypeChecker_Env.current_module
                                                       env
                                                      in
                                                   uu____8685.FStar_Ident.str
                                                    in
                                                 FStar_Options.dont_gen_projectors
                                                   uu____8683)
                                               in
                                            let no_decl = false  in
                                            let quals q =
                                              if only_decl
                                              then
                                                let uu____8704 =
                                                  FStar_List.filter
                                                    (fun uu___5_8708  ->
                                                       match uu___5_8708 with
                                                       | FStar_Syntax_Syntax.Abstract
                                                            -> false
                                                       | uu____8711 -> true)
                                                    q
                                                   in
                                                FStar_Syntax_Syntax.Assumption
                                                  :: uu____8704
                                              else q  in
                                            let quals1 =
                                              let iquals1 =
                                                FStar_All.pipe_right iquals
                                                  (FStar_List.filter
                                                     (fun uu___6_8726  ->
                                                        match uu___6_8726
                                                        with
                                                        | FStar_Syntax_Syntax.Inline_for_extraction
                                                             -> true
                                                        | FStar_Syntax_Syntax.NoExtract
                                                             -> true
                                                        | FStar_Syntax_Syntax.Abstract
                                                             -> true
                                                        | FStar_Syntax_Syntax.Private
                                                             -> true
                                                        | uu____8732 -> false))
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
                                              let uu____8743 =
                                                FStar_Ident.range_of_lid
                                                  field_name
                                                 in
                                              {
                                                FStar_Syntax_Syntax.sigel =
                                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                                     (field_name, uvs, t));
                                                FStar_Syntax_Syntax.sigrng =
                                                  uu____8743;
                                                FStar_Syntax_Syntax.sigquals
                                                  = quals1;
                                                FStar_Syntax_Syntax.sigmeta =
                                                  FStar_Syntax_Syntax.default_sigmeta;
                                                FStar_Syntax_Syntax.sigattrs
                                                  = attrs1;
                                                FStar_Syntax_Syntax.sigopts =
                                                  FStar_Pervasives_Native.None
                                              }  in
                                            ((let uu____8745 =
                                                FStar_TypeChecker_Env.debug
                                                  env
                                                  (FStar_Options.Other
                                                     "LogTypes")
                                                 in
                                              if uu____8745
                                              then
                                                let uu____8749 =
                                                  FStar_Syntax_Print.sigelt_to_string
                                                    decl
                                                   in
                                                FStar_Util.print1
                                                  "Declaration of a projector %s\n"
                                                  uu____8749
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
                                                          fun uu____8803  ->
                                                            match uu____8803
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
                                                                  let uu____8829
                                                                    =
                                                                    pos
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    projection)
                                                                     in
                                                                  (uu____8829,
                                                                    b)
                                                                else
                                                                  if
                                                                    b &&
                                                                    (j < ntps)
                                                                  then
                                                                    (
                                                                    let uu____8845
                                                                    =
                                                                    let uu____8848
                                                                    =
                                                                    let uu____8849
                                                                    =
                                                                    let uu____8856
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    (uu____8856,
                                                                    FStar_Syntax_Syntax.tun)
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_dot_term
                                                                    uu____8849
                                                                     in
                                                                    pos
                                                                    uu____8848
                                                                     in
                                                                    (uu____8845,
                                                                    b))
                                                                  else
                                                                    (
                                                                    let uu____8864
                                                                    =
                                                                    let uu____8867
                                                                    =
                                                                    let uu____8868
                                                                    =
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    (x1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    FStar_Syntax_Syntax.Pat_wild
                                                                    uu____8868
                                                                     in
                                                                    pos
                                                                    uu____8867
                                                                     in
                                                                    (uu____8864,
                                                                    b))))
                                                   in
                                                let pat =
                                                  let uu____8887 =
                                                    let uu____8890 =
                                                      let uu____8891 =
                                                        let uu____8905 =
                                                          FStar_Syntax_Syntax.lid_as_fv
                                                            lid
                                                            FStar_Syntax_Syntax.delta_constant
                                                            (FStar_Pervasives_Native.Some
                                                               fvq)
                                                           in
                                                        (uu____8905,
                                                          arg_pats)
                                                         in
                                                      FStar_Syntax_Syntax.Pat_cons
                                                        uu____8891
                                                       in
                                                    pos uu____8890  in
                                                  let uu____8915 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      projection
                                                     in
                                                  (uu____8887,
                                                    FStar_Pervasives_Native.None,
                                                    uu____8915)
                                                   in
                                                let body =
                                                  let uu____8931 =
                                                    let uu____8938 =
                                                      let uu____8939 =
                                                        let uu____8962 =
                                                          let uu____8979 =
                                                            FStar_Syntax_Util.branch
                                                              pat
                                                             in
                                                          [uu____8979]  in
                                                        (arg_exp, uu____8962)
                                                         in
                                                      FStar_Syntax_Syntax.Tm_match
                                                        uu____8939
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      uu____8938
                                                     in
                                                  uu____8931
                                                    FStar_Pervasives_Native.None
                                                    p1
                                                   in
                                                let imp =
                                                  FStar_Syntax_Util.abs
                                                    binders body
                                                    FStar_Pervasives_Native.None
                                                   in
                                                let dd =
                                                  let uu____9044 =
                                                    FStar_All.pipe_right
                                                      quals1
                                                      (FStar_List.contains
                                                         FStar_Syntax_Syntax.Abstract)
                                                     in
                                                  if uu____9044
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
                                                  let uu____9063 =
                                                    let uu____9068 =
                                                      FStar_Syntax_Syntax.lid_as_fv
                                                        field_name dd
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    FStar_Util.Inr uu____9068
                                                     in
                                                  let uu____9069 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      uvs imp
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.lbname
                                                      = uu____9063;
                                                    FStar_Syntax_Syntax.lbunivs
                                                      = uvs;
                                                    FStar_Syntax_Syntax.lbtyp
                                                      = lbtyp;
                                                    FStar_Syntax_Syntax.lbeff
                                                      =
                                                      FStar_Parser_Const.effect_Tot_lid;
                                                    FStar_Syntax_Syntax.lbdef
                                                      = uu____9069;
                                                    FStar_Syntax_Syntax.lbattrs
                                                      = [];
                                                    FStar_Syntax_Syntax.lbpos
                                                      =
                                                      FStar_Range.dummyRange
                                                  }  in
                                                let impl =
                                                  let uu____9075 =
                                                    let uu____9076 =
                                                      let uu____9083 =
                                                        let uu____9086 =
                                                          let uu____9087 =
                                                            FStar_All.pipe_right
                                                              lb.FStar_Syntax_Syntax.lbname
                                                              FStar_Util.right
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____9087
                                                            (fun fv  ->
                                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                                           in
                                                        [uu____9086]  in
                                                      ((false, [lb]),
                                                        uu____9083)
                                                       in
                                                    FStar_Syntax_Syntax.Sig_let
                                                      uu____9076
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.sigel
                                                      = uu____9075;
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
                                                (let uu____9101 =
                                                   FStar_TypeChecker_Env.debug
                                                     env
                                                     (FStar_Options.Other
                                                        "LogTypes")
                                                    in
                                                 if uu____9101
                                                 then
                                                   let uu____9105 =
                                                     FStar_Syntax_Print.sigelt_to_string
                                                       impl
                                                      in
                                                   FStar_Util.print1
                                                     "Implementation of a projector %s\n"
                                                     uu____9105
                                                 else ());
                                                if no_decl
                                                then [impl]
                                                else [decl; impl]))))
                               in
                            FStar_All.pipe_right uu____8607
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
                (constr_lid,uvs,t,typ_lid,n_typars,uu____9168) when
                let uu____9175 =
                  FStar_Ident.lid_equals constr_lid
                    FStar_Parser_Const.lexcons_lid
                   in
                Prims.op_Negation uu____9175 ->
                let uu____9177 = FStar_Syntax_Subst.univ_var_opening uvs  in
                (match uu____9177 with
                 | (univ_opening,uvs1) ->
                     let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                     let uu____9199 = FStar_Syntax_Util.arrow_formals t1  in
                     (match uu____9199 with
                      | (formals,uu____9209) ->
                          let uu____9214 =
                            let tps_opt =
                              FStar_Util.find_map tcs
                                (fun se1  ->
                                   let uu____9249 =
                                     let uu____9251 =
                                       let uu____9252 =
                                         FStar_Syntax_Util.lid_of_sigelt se1
                                          in
                                       FStar_Util.must uu____9252  in
                                     FStar_Ident.lid_equals typ_lid
                                       uu____9251
                                      in
                                   if uu____9249
                                   then
                                     match se1.FStar_Syntax_Syntax.sigel with
                                     | FStar_Syntax_Syntax.Sig_inductive_typ
                                         (uu____9274,uvs',tps,typ0,uu____9278,constrs)
                                         ->
                                         FStar_Pervasives_Native.Some
                                           (tps, typ0,
                                             ((FStar_List.length constrs) >
                                                Prims.int_one))
                                     | uu____9298 -> failwith "Impossible"
                                   else FStar_Pervasives_Native.None)
                               in
                            match tps_opt with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                let uu____9347 =
                                  FStar_Ident.lid_equals typ_lid
                                    FStar_Parser_Const.exn_lid
                                   in
                                if uu____9347
                                then ([], FStar_Syntax_Util.ktype0, true)
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnexpectedDataConstructor,
                                      "Unexpected data constructor")
                                    se.FStar_Syntax_Syntax.sigrng
                             in
                          (match uu____9214 with
                           | (inductive_tps,typ0,should_refine) ->
                               let inductive_tps1 =
                                 FStar_Syntax_Subst.subst_binders
                                   univ_opening inductive_tps
                                  in
                               let typ01 =
                                 FStar_Syntax_Subst.subst univ_opening typ0
                                  in
                               let uu____9385 =
                                 FStar_Syntax_Util.arrow_formals typ01  in
                               (match uu____9385 with
                                | (indices,uu____9395) ->
                                    let refine_domain =
                                      let uu____9402 =
                                        FStar_All.pipe_right
                                          se.FStar_Syntax_Syntax.sigquals
                                          (FStar_Util.for_some
                                             (fun uu___7_9409  ->
                                                match uu___7_9409 with
                                                | FStar_Syntax_Syntax.RecordConstructor
                                                    uu____9411 -> true
                                                | uu____9421 -> false))
                                         in
                                      if uu____9402
                                      then false
                                      else should_refine  in
                                    let fv_qual =
                                      let filter_records uu___8_9436 =
                                        match uu___8_9436 with
                                        | FStar_Syntax_Syntax.RecordConstructor
                                            (uu____9439,fns) ->
                                            FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Syntax.Record_ctor
                                                 (typ_lid, fns))
                                        | uu____9451 ->
                                            FStar_Pervasives_Native.None
                                         in
                                      let uu____9452 =
                                        FStar_Util.find_map
                                          se.FStar_Syntax_Syntax.sigquals
                                          filter_records
                                         in
                                      match uu____9452 with
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
                                      let uu____9465 =
                                        FStar_Util.first_N n_typars formals
                                         in
                                      match uu____9465 with
                                      | (imp_tps,fields) ->
                                          let rename =
                                            FStar_List.map2
                                              (fun uu____9548  ->
                                                 fun uu____9549  ->
                                                   match (uu____9548,
                                                           uu____9549)
                                                   with
                                                   | ((x,uu____9575),
                                                      (x',uu____9577)) ->
                                                       let uu____9598 =
                                                         let uu____9605 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x'
                                                            in
                                                         (x, uu____9605)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____9598) imp_tps
                                              inductive_tps1
                                             in
                                          FStar_Syntax_Subst.subst_binders
                                            rename fields
                                       in
                                    let erasable =
                                      FStar_Syntax_Util.has_attribute
                                        se.FStar_Syntax_Syntax.sigattrs
                                        FStar_Parser_Const.erasable_attr
                                       in
                                    mk_discriminator_and_indexed_projectors
                                      iquals1 attrs fv_qual refine_domain env
                                      typ_lid constr_lid uvs1 inductive_tps1
                                      indices fields erasable))))
            | uu____9612 -> []
  