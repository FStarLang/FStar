open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__env : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts,FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___348_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___348_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___348_123.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____124
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____134 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____134
             then
               (d "Elaborating extra WP combinators";
                (let uu____136 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____136))
             else ());
            (let rec collect_binders t =
               let uu____152 =
                 let uu____153 =
                   let uu____156 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____156
                    in
                 uu____153.FStar_Syntax_Syntax.n  in
               match uu____152 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____191) -> t1
                     | uu____200 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____201 = collect_binders rest  in
                   FStar_List.append bs uu____201
               | FStar_Syntax_Syntax.Tm_type uu____216 -> []
               | uu____223 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____247 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____247 FStar_Syntax_Util.name_binders
                in
             (let uu____273 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____273
              then
                let uu____274 =
                  let uu____275 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____275  in
                d uu____274
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____311 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____311 with
                | (sigelt,fv) ->
                    ((let uu____325 =
                        let uu____328 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____328
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____325);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____450  ->
                     match uu____450 with
                     | (t,b) ->
                         let uu____461 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____461))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____500 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____500))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____533 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____533)
                 in
              let uu____536 =
                let uu____553 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____577 =
                        let uu____580 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____580  in
                      FStar_Syntax_Util.arrow gamma uu____577  in
                    let uu____581 =
                      let uu____582 =
                        let uu____591 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____598 =
                          let uu____607 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____607]  in
                        uu____591 :: uu____598  in
                      FStar_List.append binders uu____582  in
                    FStar_Syntax_Util.abs uu____581 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____638 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____639 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____638, uu____639)  in
                match uu____553 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____683 =
                        let uu____684 =
                          let uu____701 =
                            let uu____712 =
                              FStar_List.map
                                (fun uu____734  ->
                                   match uu____734 with
                                   | (bv,uu____746) ->
                                       let uu____751 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____752 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____751, uu____752)) binders
                               in
                            let uu____753 =
                              let uu____760 =
                                let uu____765 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____766 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____765, uu____766)  in
                              let uu____767 =
                                let uu____774 =
                                  let uu____779 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____779)  in
                                [uu____774]  in
                              uu____760 :: uu____767  in
                            FStar_List.append uu____712 uu____753  in
                          (fv, uu____701)  in
                        FStar_Syntax_Syntax.Tm_app uu____684  in
                      mk1 uu____683  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____536 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____850 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____850
                       in
                    let ret1 =
                      let uu____854 =
                        let uu____855 =
                          let uu____858 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____858  in
                        FStar_Syntax_Util.residual_tot uu____855  in
                      FStar_Pervasives_Native.Some uu____854  in
                    let body =
                      let uu____862 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____862 ret1  in
                    let uu____865 =
                      let uu____866 = mk_all_implicit binders  in
                      let uu____873 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____866 uu____873  in
                    FStar_Syntax_Util.abs uu____865 body ret1  in
                  let c_pure1 =
                    let uu____903 = mk_lid "pure"  in
                    register env1 uu____903 c_pure  in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let l =
                      let uu____910 =
                        let uu____911 =
                          let uu____912 =
                            let uu____921 =
                              let uu____928 =
                                let uu____929 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____929
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____928  in
                            [uu____921]  in
                          let uu____942 =
                            let uu____945 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____945  in
                          FStar_Syntax_Util.arrow uu____912 uu____942  in
                        mk_gctx uu____911  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____910
                       in
                    let r =
                      let uu____947 =
                        let uu____948 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____948  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____947
                       in
                    let ret1 =
                      let uu____952 =
                        let uu____953 =
                          let uu____956 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____956  in
                        FStar_Syntax_Util.residual_tot uu____953  in
                      FStar_Pervasives_Native.Some uu____952  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____966 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____969 =
                          let uu____980 =
                            let uu____983 =
                              let uu____984 =
                                let uu____985 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____985
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____984  in
                            [uu____983]  in
                          FStar_List.append gamma_as_args uu____980  in
                        FStar_Syntax_Util.mk_app uu____966 uu____969  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____988 =
                      let uu____989 = mk_all_implicit binders  in
                      let uu____996 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____989 uu____996  in
                    FStar_Syntax_Util.abs uu____988 outer_body ret1  in
                  let c_app1 =
                    let uu____1034 = mk_lid "app"  in
                    register env1 uu____1034 c_app  in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1043 =
                        let uu____1052 =
                          let uu____1059 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1059  in
                        [uu____1052]  in
                      let uu____1072 =
                        let uu____1075 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1075  in
                      FStar_Syntax_Util.arrow uu____1043 uu____1072  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1078 =
                        let uu____1079 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1079  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1078
                       in
                    let ret1 =
                      let uu____1083 =
                        let uu____1084 =
                          let uu____1087 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1087  in
                        FStar_Syntax_Util.residual_tot uu____1084  in
                      FStar_Pervasives_Native.Some uu____1083  in
                    let uu____1088 =
                      let uu____1089 = mk_all_implicit binders  in
                      let uu____1096 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1089 uu____1096  in
                    let uu____1131 =
                      let uu____1134 =
                        let uu____1145 =
                          let uu____1148 =
                            let uu____1149 =
                              let uu____1160 =
                                let uu____1163 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1163]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1160
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1149  in
                          let uu____1172 =
                            let uu____1175 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1175]  in
                          uu____1148 :: uu____1172  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1145
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1134  in
                    FStar_Syntax_Util.abs uu____1088 uu____1131 ret1  in
                  let c_lift11 =
                    let uu____1187 = mk_lid "lift1"  in
                    register env1 uu____1187 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1197 =
                        let uu____1206 =
                          let uu____1213 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1213  in
                        let uu____1214 =
                          let uu____1223 =
                            let uu____1230 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1230  in
                          [uu____1223]  in
                        uu____1206 :: uu____1214  in
                      let uu____1249 =
                        let uu____1252 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1252  in
                      FStar_Syntax_Util.arrow uu____1197 uu____1249  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1255 =
                        let uu____1256 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1256  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1255
                       in
                    let a2 =
                      let uu____1258 =
                        let uu____1259 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1259  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1258
                       in
                    let ret1 =
                      let uu____1263 =
                        let uu____1264 =
                          let uu____1267 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1267  in
                        FStar_Syntax_Util.residual_tot uu____1264  in
                      FStar_Pervasives_Native.Some uu____1263  in
                    let uu____1268 =
                      let uu____1269 = mk_all_implicit binders  in
                      let uu____1276 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1269 uu____1276  in
                    let uu____1319 =
                      let uu____1322 =
                        let uu____1333 =
                          let uu____1336 =
                            let uu____1337 =
                              let uu____1348 =
                                let uu____1351 =
                                  let uu____1352 =
                                    let uu____1363 =
                                      let uu____1366 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1366]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1363
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1352
                                   in
                                let uu____1375 =
                                  let uu____1378 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1378]  in
                                uu____1351 :: uu____1375  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1348
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1337  in
                          let uu____1387 =
                            let uu____1390 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1390]  in
                          uu____1336 :: uu____1387  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1333
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1322  in
                    FStar_Syntax_Util.abs uu____1268 uu____1319 ret1  in
                  let c_lift21 =
                    let uu____1402 = mk_lid "lift2"  in
                    register env1 uu____1402 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1411 =
                        let uu____1420 =
                          let uu____1427 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1427  in
                        [uu____1420]  in
                      let uu____1440 =
                        let uu____1443 =
                          let uu____1444 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1444  in
                        FStar_Syntax_Syntax.mk_Total uu____1443  in
                      FStar_Syntax_Util.arrow uu____1411 uu____1440  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1449 =
                        let uu____1450 =
                          let uu____1453 =
                            let uu____1454 =
                              let uu____1463 =
                                let uu____1470 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1470
                                 in
                              [uu____1463]  in
                            let uu____1483 =
                              let uu____1486 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1486  in
                            FStar_Syntax_Util.arrow uu____1454 uu____1483  in
                          mk_ctx uu____1453  in
                        FStar_Syntax_Util.residual_tot uu____1450  in
                      FStar_Pervasives_Native.Some uu____1449  in
                    let e1 =
                      let uu____1488 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1488
                       in
                    let body =
                      let uu____1492 =
                        let uu____1493 =
                          let uu____1502 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1502]  in
                        FStar_List.append gamma uu____1493  in
                      let uu____1527 =
                        let uu____1530 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1533 =
                          let uu____1544 =
                            let uu____1545 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1545  in
                          let uu____1546 = args_of_binders1 gamma  in
                          uu____1544 :: uu____1546  in
                        FStar_Syntax_Util.mk_app uu____1530 uu____1533  in
                      FStar_Syntax_Util.abs uu____1492 uu____1527 ret1  in
                    let uu____1549 =
                      let uu____1550 = mk_all_implicit binders  in
                      let uu____1557 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1550 uu____1557  in
                    FStar_Syntax_Util.abs uu____1549 body ret1  in
                  let c_push1 =
                    let uu____1591 = mk_lid "push"  in
                    register env1 uu____1591 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1615 =
                        let uu____1616 =
                          let uu____1633 = args_of_binders1 binders  in
                          (c, uu____1633)  in
                        FStar_Syntax_Syntax.Tm_app uu____1616  in
                      mk1 uu____1615
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1661 =
                        let uu____1662 =
                          let uu____1671 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1678 =
                            let uu____1687 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1687]  in
                          uu____1671 :: uu____1678  in
                        let uu____1712 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1662 uu____1712  in
                      FStar_Syntax_Syntax.mk_Total uu____1661  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1716 =
                      let uu____1717 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1717  in
                    let uu____1732 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1736 =
                        let uu____1739 =
                          let uu____1750 =
                            let uu____1753 =
                              let uu____1754 =
                                let uu____1765 =
                                  let uu____1774 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1774  in
                                [uu____1765]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1754  in
                            [uu____1753]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1750
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1739  in
                      FStar_Syntax_Util.ascribe uu____1736
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1716 uu____1732
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1820 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1820 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1833 =
                        let uu____1844 =
                          let uu____1847 =
                            let uu____1848 =
                              let uu____1859 =
                                let uu____1862 =
                                  let uu____1863 =
                                    let uu____1874 =
                                      let uu____1883 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1883
                                       in
                                    [uu____1874]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1863
                                   in
                                [uu____1862]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1859
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1848  in
                          let uu____1908 =
                            let uu____1911 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1911]  in
                          uu____1847 :: uu____1908  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1844
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1833  in
                    let uu____1920 =
                      let uu____1921 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1921  in
                    FStar_Syntax_Util.abs uu____1920 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1939 = mk_lid "wp_assert"  in
                    register env1 uu____1939 wp_assert  in
                  let wp_assert2 = mk_generic_app wp_assert1  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1952 =
                        let uu____1963 =
                          let uu____1966 =
                            let uu____1967 =
                              let uu____1978 =
                                let uu____1981 =
                                  let uu____1982 =
                                    let uu____1993 =
                                      let uu____2002 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2002
                                       in
                                    [uu____1993]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1982
                                   in
                                [uu____1981]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1978
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1967  in
                          let uu____2027 =
                            let uu____2030 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2030]  in
                          uu____1966 :: uu____2027  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1963
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1952  in
                    let uu____2039 =
                      let uu____2040 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2040  in
                    FStar_Syntax_Util.abs uu____2039 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2058 = mk_lid "wp_assume"  in
                    register env1 uu____2058 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2069 =
                        let uu____2078 =
                          let uu____2085 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2085  in
                        [uu____2078]  in
                      let uu____2098 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2069 uu____2098  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2105 =
                        let uu____2116 =
                          let uu____2119 =
                            let uu____2120 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2120  in
                          let uu____2139 =
                            let uu____2142 =
                              let uu____2143 =
                                let uu____2154 =
                                  let uu____2157 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2157]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2154
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2143  in
                            [uu____2142]  in
                          uu____2119 :: uu____2139  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2116
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2105  in
                    let uu____2174 =
                      let uu____2175 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2175  in
                    FStar_Syntax_Util.abs uu____2174 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2193 = mk_lid "wp_close"  in
                    register env1 uu____2193 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2203 =
                      let uu____2204 =
                        let uu____2205 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2205
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2204  in
                    FStar_Pervasives_Native.Some uu____2203  in
                  let mk_forall1 x body =
                    let uu____2217 =
                      let uu____2224 =
                        let uu____2225 =
                          let uu____2242 =
                            let uu____2253 =
                              let uu____2262 =
                                let uu____2263 =
                                  let uu____2264 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2264]  in
                                FStar_Syntax_Util.abs uu____2263 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2262  in
                            [uu____2253]  in
                          (FStar_Syntax_Util.tforall, uu____2242)  in
                        FStar_Syntax_Syntax.Tm_app uu____2225  in
                      FStar_Syntax_Syntax.mk uu____2224  in
                    uu____2217 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2324 =
                      let uu____2325 = FStar_Syntax_Subst.compress t  in
                      uu____2325.FStar_Syntax_Syntax.n  in
                    match uu____2324 with
                    | FStar_Syntax_Syntax.Tm_type uu____2328 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2360  ->
                              match uu____2360 with
                              | (b,uu____2368) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2373 -> true  in
                  let rec is_monotonic t =
                    let uu____2384 =
                      let uu____2385 = FStar_Syntax_Subst.compress t  in
                      uu____2385.FStar_Syntax_Syntax.n  in
                    match uu____2384 with
                    | FStar_Syntax_Syntax.Tm_type uu____2388 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2420  ->
                              match uu____2420 with
                              | (b,uu____2428) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2433 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2507 =
                      let uu____2508 = FStar_Syntax_Subst.compress t1  in
                      uu____2508.FStar_Syntax_Syntax.n  in
                    match uu____2507 with
                    | FStar_Syntax_Syntax.Tm_type uu____2513 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2516);
                                      FStar_Syntax_Syntax.pos = uu____2517;
                                      FStar_Syntax_Syntax.vars = uu____2518;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2562 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2562
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2569 =
                              let uu____2572 =
                                let uu____2583 =
                                  let uu____2592 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2592  in
                                [uu____2583]  in
                              FStar_Syntax_Util.mk_app x uu____2572  in
                            let uu____2609 =
                              let uu____2612 =
                                let uu____2623 =
                                  let uu____2632 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2632  in
                                [uu____2623]  in
                              FStar_Syntax_Util.mk_app y uu____2612  in
                            mk_rel1 b uu____2569 uu____2609  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____2653 =
                               let uu____2656 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2659 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2656 uu____2659  in
                             let uu____2662 =
                               let uu____2665 =
                                 let uu____2668 =
                                   let uu____2679 =
                                     let uu____2688 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2688
                                      in
                                   [uu____2679]  in
                                 FStar_Syntax_Util.mk_app x uu____2668  in
                               let uu____2705 =
                                 let uu____2708 =
                                   let uu____2719 =
                                     let uu____2728 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2728
                                      in
                                   [uu____2719]  in
                                 FStar_Syntax_Util.mk_app y uu____2708  in
                               mk_rel1 b uu____2665 uu____2705  in
                             FStar_Syntax_Util.mk_imp uu____2653 uu____2662
                              in
                           let uu____2745 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2745)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2748);
                                      FStar_Syntax_Syntax.pos = uu____2749;
                                      FStar_Syntax_Syntax.vars = uu____2750;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2794 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2794
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2801 =
                              let uu____2804 =
                                let uu____2815 =
                                  let uu____2824 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2824  in
                                [uu____2815]  in
                              FStar_Syntax_Util.mk_app x uu____2804  in
                            let uu____2841 =
                              let uu____2844 =
                                let uu____2855 =
                                  let uu____2864 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2864  in
                                [uu____2855]  in
                              FStar_Syntax_Util.mk_app y uu____2844  in
                            mk_rel1 b uu____2801 uu____2841  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____2885 =
                               let uu____2888 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2891 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2888 uu____2891  in
                             let uu____2894 =
                               let uu____2897 =
                                 let uu____2900 =
                                   let uu____2911 =
                                     let uu____2920 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2920
                                      in
                                   [uu____2911]  in
                                 FStar_Syntax_Util.mk_app x uu____2900  in
                               let uu____2937 =
                                 let uu____2940 =
                                   let uu____2951 =
                                     let uu____2960 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2960
                                      in
                                   [uu____2951]  in
                                 FStar_Syntax_Util.mk_app y uu____2940  in
                               mk_rel1 b uu____2897 uu____2937  in
                             FStar_Syntax_Util.mk_imp uu____2885 uu____2894
                              in
                           let uu____2977 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2977)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___349_3016 = t1  in
                          let uu____3017 =
                            let uu____3018 =
                              let uu____3033 =
                                let uu____3036 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3036  in
                              ([binder], uu____3033)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3018  in
                          {
                            FStar_Syntax_Syntax.n = uu____3017;
                            FStar_Syntax_Syntax.pos =
                              (uu___349_3016.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___349_3016.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3059 ->
                        failwith "unhandled arrow"
                    | uu____3076 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env1 t
                         in
                      let uu____3111 =
                        let uu____3112 = FStar_Syntax_Subst.compress t1  in
                        uu____3112.FStar_Syntax_Syntax.n  in
                      match uu____3111 with
                      | FStar_Syntax_Syntax.Tm_type uu____3115 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3142 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3142
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3161 =
                                let uu____3162 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3162 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3161
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3191 =
                            let uu____3202 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3220  ->
                                     match uu____3220 with
                                     | (t2,q) ->
                                         let uu____3239 = project i x  in
                                         let uu____3242 = project i y  in
                                         mk_stronger t2 uu____3239 uu____3242)
                                args
                               in
                            match uu____3202 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3191 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3295);
                                      FStar_Syntax_Syntax.pos = uu____3296;
                                      FStar_Syntax_Syntax.vars = uu____3297;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3341  ->
                                   match uu____3341 with
                                   | (bv,q) ->
                                       let uu____3354 =
                                         let uu____3355 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3355  in
                                       FStar_Syntax_Syntax.gen_bv uu____3354
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3362 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3362) bvs
                             in
                          let body =
                            let uu____3364 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3367 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3364 uu____3367  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3376);
                                      FStar_Syntax_Syntax.pos = uu____3377;
                                      FStar_Syntax_Syntax.vars = uu____3378;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3422  ->
                                   match uu____3422 with
                                   | (bv,q) ->
                                       let uu____3435 =
                                         let uu____3436 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3436  in
                                       FStar_Syntax_Syntax.gen_bv uu____3435
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3443 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3443) bvs
                             in
                          let body =
                            let uu____3445 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3448 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3445 uu____3448  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3455 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3457 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3460 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3463 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3457 uu____3460 uu____3463  in
                    let uu____3466 =
                      let uu____3467 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3467  in
                    FStar_Syntax_Util.abs uu____3466 body ret_tot_type  in
                  let stronger1 =
                    let uu____3501 = mk_lid "stronger"  in
                    register env1 uu____3501 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3507 = FStar_Util.prefix gamma  in
                    match uu____3507 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3572 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3572
                             in
                          let uu____3577 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3577 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3629 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3629  in
                              let guard_free1 =
                                let uu____3641 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3641  in
                              let pat =
                                let uu____3645 =
                                  let uu____3656 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3656]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3645
                                 in
                              let pattern_guarded_body =
                                let uu____3684 =
                                  let uu____3685 =
                                    let uu____3692 =
                                      let uu____3693 =
                                        let uu____3706 =
                                          let uu____3717 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3717]  in
                                        [uu____3706]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3693
                                       in
                                    (body, uu____3692)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3685  in
                                mk1 uu____3684  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3764 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3772 =
                            let uu____3775 =
                              let uu____3776 =
                                let uu____3779 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3782 =
                                  let uu____3793 = args_of_binders1 wp_args
                                     in
                                  let uu____3796 =
                                    let uu____3799 =
                                      let uu____3800 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3800
                                       in
                                    [uu____3799]  in
                                  FStar_List.append uu____3793 uu____3796  in
                                FStar_Syntax_Util.mk_app uu____3779
                                  uu____3782
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3776  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3775
                             in
                          FStar_Syntax_Util.abs gamma uu____3772
                            ret_gtot_type
                           in
                        let uu____3801 =
                          let uu____3802 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3802  in
                        FStar_Syntax_Util.abs uu____3801 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3820 = mk_lid "wp_ite"  in
                    register env1 uu____3820 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3826 = FStar_Util.prefix gamma  in
                    match uu____3826 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3883 =
                            let uu____3884 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3891 =
                              let uu____3902 =
                                let uu____3911 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3911  in
                              [uu____3902]  in
                            FStar_Syntax_Util.mk_app uu____3884 uu____3891
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3883
                           in
                        let uu____3928 =
                          let uu____3929 =
                            let uu____3938 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3938 gamma  in
                          FStar_List.append binders uu____3929  in
                        FStar_Syntax_Util.abs uu____3928 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3962 = mk_lid "null_wp"  in
                    register env1 uu____3962 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3973 =
                        let uu____3984 =
                          let uu____3987 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3988 =
                            let uu____3991 =
                              let uu____3992 =
                                let uu____4003 =
                                  let uu____4012 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4012  in
                                [uu____4003]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3992
                               in
                            let uu____4029 =
                              let uu____4032 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4032]  in
                            uu____3991 :: uu____4029  in
                          uu____3987 :: uu____3988  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3984
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3973  in
                    let uu____4041 =
                      let uu____4042 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4042  in
                    FStar_Syntax_Util.abs uu____4041 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4060 = mk_lid "wp_trivial"  in
                    register env1 uu____4060 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4065 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4065
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4072 =
                      let uu____4073 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4073  in
                    let uu____4121 =
                      let uu___350_4122 = ed  in
                      let uu____4123 =
                        let uu____4124 = c wp_if_then_else2  in
                        ([], uu____4124)  in
                      let uu____4131 =
                        let uu____4132 = c wp_ite2  in ([], uu____4132)  in
                      let uu____4139 =
                        let uu____4140 = c stronger2  in ([], uu____4140)  in
                      let uu____4147 =
                        let uu____4148 = c wp_close2  in ([], uu____4148)  in
                      let uu____4155 =
                        let uu____4156 = c wp_assert2  in ([], uu____4156)
                         in
                      let uu____4163 =
                        let uu____4164 = c wp_assume2  in ([], uu____4164)
                         in
                      let uu____4171 =
                        let uu____4172 = c null_wp2  in ([], uu____4172)  in
                      let uu____4179 =
                        let uu____4180 = c wp_trivial2  in ([], uu____4180)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___350_4122.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___350_4122.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___350_4122.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___350_4122.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___350_4122.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___350_4122.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___350_4122.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____4123;
                        FStar_Syntax_Syntax.ite_wp = uu____4131;
                        FStar_Syntax_Syntax.stronger = uu____4139;
                        FStar_Syntax_Syntax.close_wp = uu____4147;
                        FStar_Syntax_Syntax.assert_p = uu____4155;
                        FStar_Syntax_Syntax.assume_p = uu____4163;
                        FStar_Syntax_Syntax.null_wp = uu____4171;
                        FStar_Syntax_Syntax.trivial = uu____4179;
                        FStar_Syntax_Syntax.repr =
                          (uu___350_4122.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___350_4122.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___350_4122.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___350_4122.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___350_4122.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4072, uu____4121)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___351_4202 = dmff_env  in
      {
        env = env';
        subst = (uu___351_4202.subst);
        tc_const = (uu___351_4202.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4219 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4233 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___337_4245  ->
    match uu___337_4245 with
    | FStar_Syntax_Syntax.Total (t,uu____4247) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___336_4260  ->
                match uu___336_4260 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4261 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____4263 =
          let uu____4264 =
            let uu____4265 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____4265
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____4264  in
        failwith uu____4263
    | FStar_Syntax_Syntax.GTotal uu____4266 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___338_4279  ->
    match uu___338_4279 with
    | N t ->
        let uu____4281 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4281
    | M t ->
        let uu____4283 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4283
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____4289,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____4291;
                      FStar_Syntax_Syntax.vars = uu____4292;_})
        -> nm_of_comp n2
    | uu____4313 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4323 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____4323 with | M uu____4324 -> true | N uu____4325 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4331 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4345 =
        let uu____4354 =
          let uu____4361 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4361  in
        [uu____4354]  in
      let uu____4380 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4345 uu____4380  in
    let uu____4383 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4383
  
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        let uu____4424 =
          let uu____4425 =
            let uu____4440 =
              let uu____4449 =
                let uu____4456 =
                  let uu____4457 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4457  in
                let uu____4458 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4456, uu____4458)  in
              [uu____4449]  in
            let uu____4475 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4440, uu____4475)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4425  in
        mk1 uu____4424

and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type1 = mk_star_to_type mk1  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4515) ->
          let binders1 =
            FStar_List.map
              (fun uu____4561  ->
                 match uu____4561 with
                 | (bv,aqual) ->
                     let uu____4580 =
                       let uu___352_4581 = bv  in
                       let uu____4582 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___352_4581.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___352_4581.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4582
                       }  in
                     (uu____4580, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4587,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4589);
                             FStar_Syntax_Syntax.pos = uu____4590;
                             FStar_Syntax_Syntax.vars = uu____4591;_})
               ->
               let uu____4620 =
                 let uu____4621 =
                   let uu____4636 =
                     let uu____4639 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4639  in
                   (binders1, uu____4636)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4621  in
               mk1 uu____4620
           | uu____4650 ->
               let uu____4651 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4651 with
                | N hn ->
                    let uu____4653 =
                      let uu____4654 =
                        let uu____4669 =
                          let uu____4672 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4672  in
                        (binders1, uu____4669)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4654  in
                    mk1 uu____4653
                | M a ->
                    let uu____4684 =
                      let uu____4685 =
                        let uu____4700 =
                          let uu____4709 =
                            let uu____4718 =
                              let uu____4725 =
                                let uu____4726 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4726  in
                              let uu____4727 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4725, uu____4727)  in
                            [uu____4718]  in
                          FStar_List.append binders1 uu____4709  in
                        let uu____4750 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4700, uu____4750)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4685  in
                    mk1 uu____4684))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4838 = f x  in
                    FStar_Util.string_builder_append strb uu____4838);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4845 = f x1  in
                         FStar_Util.string_builder_append strb uu____4845))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4847 =
              let uu____4852 =
                let uu____4853 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4854 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4853 uu____4854
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4852)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4847  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4870 =
              let uu____4871 = FStar_Syntax_Subst.compress ty  in
              uu____4871.FStar_Syntax_Syntax.n  in
            match uu____4870 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4896 =
                  let uu____4897 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4897  in
                if uu____4896
                then false
                else
                  (try
                     (fun uu___354_4908  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4931 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4931 s  in
                              let uu____4934 =
                                let uu____4935 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4935  in
                              if uu____4934
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4938 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4938 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4982  ->
                                          match uu____4982 with
                                          | (bv,uu____4994) ->
                                              (non_dependent_or_raise s
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s))
                                     FStar_Syntax_Syntax.no_names binders1
                                    in
                                 let ct = FStar_Syntax_Util.comp_result c1
                                    in
                                 (non_dependent_or_raise s ct;
                                  (let k = n1 - (FStar_List.length binders1)
                                      in
                                   if k > (Prims.parse_int "0")
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found  -> false)
            | uu____5014 ->
                ((let uu____5016 =
                    let uu____5021 =
                      let uu____5022 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5022
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5021)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5016);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5033 =
              let uu____5034 = FStar_Syntax_Subst.compress head2  in
              uu____5034.FStar_Syntax_Syntax.n  in
            match uu____5033 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid))
                  ||
                  (let uu____5039 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5039)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5041 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5041 with
                 | ((uu____5050,ty),uu____5052) ->
                     let uu____5069 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5069
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.env t1
                          in
                       let uu____5079 =
                         let uu____5080 = FStar_Syntax_Subst.compress res  in
                         uu____5080.FStar_Syntax_Syntax.n  in
                       (match uu____5079 with
                        | FStar_Syntax_Syntax.Tm_app uu____5083 -> true
                        | uu____5100 ->
                            ((let uu____5102 =
                                let uu____5107 =
                                  let uu____5108 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5108
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5107)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5102);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5110 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5111 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5113) ->
                is_valid_application t2
            | uu____5122 -> false  in
          let uu____5123 = is_valid_application head1  in
          if uu____5123
          then
            let uu____5124 =
              let uu____5125 =
                let uu____5142 =
                  FStar_List.map
                    (fun uu____5171  ->
                       match uu____5171 with
                       | (t2,qual) ->
                           let uu____5196 = star_type' env t2  in
                           (uu____5196, qual)) args
                   in
                (head1, uu____5142)  in
              FStar_Syntax_Syntax.Tm_app uu____5125  in
            mk1 uu____5124
          else
            (let uu____5212 =
               let uu____5217 =
                 let uu____5218 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5218
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5217)  in
             FStar_Errors.raise_err uu____5212)
      | FStar_Syntax_Syntax.Tm_bvar uu____5219 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5220 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5221 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5222 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5250 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5250 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___355_5278 = env  in
                 let uu____5279 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____5279;
                   subst = (uu___355_5278.subst);
                   tc_const = (uu___355_5278.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)]
             in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))]
             in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___356_5301 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___356_5301.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___356_5301.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5308 =
            let uu____5309 =
              let uu____5316 = star_type' env t2  in (uu____5316, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5309  in
          mk1 uu____5308
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5368 =
            let uu____5369 =
              let uu____5396 = star_type' env e  in
              let uu____5399 =
                let uu____5416 =
                  let uu____5425 = star_type' env t2  in
                  FStar_Util.Inl uu____5425  in
                (uu____5416, FStar_Pervasives_Native.None)  in
              (uu____5396, uu____5399, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5369  in
          mk1 uu____5368
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5513 =
            let uu____5514 =
              let uu____5541 = star_type' env e  in
              let uu____5544 =
                let uu____5561 =
                  let uu____5570 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5570  in
                (uu____5561, FStar_Pervasives_Native.None)  in
              (uu____5541, uu____5544, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5514  in
          mk1 uu____5513
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5611,(uu____5612,FStar_Pervasives_Native.Some uu____5613),uu____5614)
          ->
          let uu____5663 =
            let uu____5668 =
              let uu____5669 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5669
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5668)  in
          FStar_Errors.raise_err uu____5663
      | FStar_Syntax_Syntax.Tm_refine uu____5670 ->
          let uu____5677 =
            let uu____5682 =
              let uu____5683 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5683
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5682)  in
          FStar_Errors.raise_err uu____5677
      | FStar_Syntax_Syntax.Tm_uinst uu____5684 ->
          let uu____5691 =
            let uu____5696 =
              let uu____5697 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5697
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5696)  in
          FStar_Errors.raise_err uu____5691
      | FStar_Syntax_Syntax.Tm_quoted uu____5698 ->
          let uu____5705 =
            let uu____5710 =
              let uu____5711 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5711
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5710)  in
          FStar_Errors.raise_err uu____5705
      | FStar_Syntax_Syntax.Tm_constant uu____5712 ->
          let uu____5713 =
            let uu____5718 =
              let uu____5719 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5719
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5718)  in
          FStar_Errors.raise_err uu____5713
      | FStar_Syntax_Syntax.Tm_match uu____5720 ->
          let uu____5743 =
            let uu____5748 =
              let uu____5749 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5749
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5748)  in
          FStar_Errors.raise_err uu____5743
      | FStar_Syntax_Syntax.Tm_let uu____5750 ->
          let uu____5763 =
            let uu____5768 =
              let uu____5769 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5769
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5768)  in
          FStar_Errors.raise_err uu____5763
      | FStar_Syntax_Syntax.Tm_uvar uu____5770 ->
          let uu____5783 =
            let uu____5788 =
              let uu____5789 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5789
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5788)  in
          FStar_Errors.raise_err uu____5783
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5790 =
            let uu____5795 =
              let uu____5796 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5796
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5795)  in
          FStar_Errors.raise_err uu____5790
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5798 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5798
      | FStar_Syntax_Syntax.Tm_delayed uu____5801 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___340_5830  ->
    match uu___340_5830 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___339_5837  ->
                match uu___339_5837 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5838 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5844 =
      let uu____5845 = FStar_Syntax_Subst.compress t  in
      uu____5845.FStar_Syntax_Syntax.n  in
    match uu____5844 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5875 =
            let uu____5876 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5876  in
          is_C uu____5875  in
        if r
        then
          ((let uu____5898 =
              let uu____5899 =
                FStar_List.for_all
                  (fun uu____5909  ->
                     match uu____5909 with | (h,uu____5917) -> is_C h) args
                 in
              Prims.op_Negation uu____5899  in
            if uu____5898 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5925 =
              let uu____5926 =
                FStar_List.for_all
                  (fun uu____5937  ->
                     match uu____5937 with
                     | (h,uu____5945) ->
                         let uu____5950 = is_C h  in
                         Prims.op_Negation uu____5950) args
                 in
              Prims.op_Negation uu____5926  in
            if uu____5925 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5974 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5974 with
         | M t1 ->
             ((let uu____5977 = is_C t1  in
               if uu____5977 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5981) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5987) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5997,uu____5998) -> is_C t1
    | uu____6039 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk1 env t  in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type
           in
        let body =
          let uu____6072 =
            let uu____6073 =
              let uu____6090 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6093 =
                let uu____6104 =
                  let uu____6113 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6113)  in
                [uu____6104]  in
              (uu____6090, uu____6093)  in
            FStar_Syntax_Syntax.Tm_app uu____6073  in
          mk1 uu____6072  in
        let uu____6148 =
          let uu____6149 = FStar_Syntax_Syntax.mk_binder p  in [uu____6149]
           in
        FStar_Syntax_Util.abs uu____6148 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___341_6172  ->
    match uu___341_6172 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6173 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6408 =
          match uu____6408 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6445 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6447 =
                       let uu____6448 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6448  in
                     Prims.op_Negation uu____6447)
                   in
                if uu____6445
                then
                  let uu____6449 =
                    let uu____6454 =
                      let uu____6455 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6456 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6457 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6455 uu____6456 uu____6457
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6454)  in
                  FStar_Errors.raise_err uu____6449
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6478 = mk_return env t1 s_e  in
                     ((M t1), uu____6478, u_e)))
               | (M t1,N t2) ->
                   let uu____6485 =
                     let uu____6490 =
                       let uu____6491 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6492 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6493 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6491 uu____6492 uu____6493
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6490)
                      in
                   FStar_Errors.raise_err uu____6485)
           in
        let ensure_m env1 e2 =
          let strip_m uu___342_6542 =
            match uu___342_6542 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6558 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6578 =
                let uu____6583 =
                  let uu____6584 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6584
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6583)  in
              FStar_Errors.raise_error uu____6578 e2.FStar_Syntax_Syntax.pos
          | M uu____6591 ->
              let uu____6592 = check env1 e2 context_nm  in
              strip_m uu____6592
           in
        let uu____6599 =
          let uu____6600 = FStar_Syntax_Subst.compress e  in
          uu____6600.FStar_Syntax_Syntax.n  in
        match uu____6599 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6609 ->
            let uu____6610 = infer env e  in return_if uu____6610
        | FStar_Syntax_Syntax.Tm_name uu____6617 ->
            let uu____6618 = infer env e  in return_if uu____6618
        | FStar_Syntax_Syntax.Tm_fvar uu____6625 ->
            let uu____6626 = infer env e  in return_if uu____6626
        | FStar_Syntax_Syntax.Tm_abs uu____6633 ->
            let uu____6652 = infer env e  in return_if uu____6652
        | FStar_Syntax_Syntax.Tm_constant uu____6659 ->
            let uu____6660 = infer env e  in return_if uu____6660
        | FStar_Syntax_Syntax.Tm_quoted uu____6667 ->
            let uu____6674 = infer env e  in return_if uu____6674
        | FStar_Syntax_Syntax.Tm_app uu____6681 ->
            let uu____6698 = infer env e  in return_if uu____6698
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6706 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6706 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6768) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6774) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6784,uu____6785) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6826 ->
            let uu____6839 =
              let uu____6840 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6840  in
            failwith uu____6839
        | FStar_Syntax_Syntax.Tm_type uu____6847 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6854 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6875 ->
            let uu____6882 =
              let uu____6883 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6883  in
            failwith uu____6882
        | FStar_Syntax_Syntax.Tm_uvar uu____6890 ->
            let uu____6903 =
              let uu____6904 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6904  in
            failwith uu____6903
        | FStar_Syntax_Syntax.Tm_delayed uu____6911 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6940 =
              let uu____6941 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6941  in
            failwith uu____6940

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env.env
         in
      let uu____6969 =
        let uu____6970 = FStar_Syntax_Subst.compress e  in
        uu____6970.FStar_Syntax_Syntax.n  in
      match uu____6969 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6988 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6988
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7039;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7040;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7046 =
                  let uu___357_7047 = rc  in
                  let uu____7048 =
                    let uu____7053 =
                      let uu____7056 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7056  in
                    FStar_Pervasives_Native.Some uu____7053  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___357_7047.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7048;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___357_7047.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7046
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___358_7068 = env  in
            let uu____7069 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____7069;
              subst = (uu___358_7068.subst);
              tc_const = (uu___358_7068.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7095  ->
                 match uu____7095 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___359_7118 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___359_7118.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___359_7118.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7119 =
            FStar_List.fold_left
              (fun uu____7150  ->
                 fun uu____7151  ->
                   match (uu____7150, uu____7151) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7209 = is_C c  in
                       if uu____7209
                       then
                         let xw =
                           let uu____7217 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7217
                            in
                         let x =
                           let uu___360_7219 = bv  in
                           let uu____7220 =
                             let uu____7223 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7223  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___360_7219.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___360_7219.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7220
                           }  in
                         let env3 =
                           let uu___361_7225 = env2  in
                           let uu____7226 =
                             let uu____7229 =
                               let uu____7230 =
                                 let uu____7237 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7237)  in
                               FStar_Syntax_Syntax.NT uu____7230  in
                             uu____7229 :: (env2.subst)  in
                           {
                             env = (uu___361_7225.env);
                             subst = uu____7226;
                             tc_const = (uu___361_7225.tc_const)
                           }  in
                         let uu____7242 =
                           let uu____7245 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7246 =
                             let uu____7249 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7249 :: acc  in
                           uu____7245 :: uu____7246  in
                         (env3, uu____7242)
                       else
                         (let x =
                            let uu___362_7254 = bv  in
                            let uu____7255 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___362_7254.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___362_7254.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7255
                            }  in
                          let uu____7258 =
                            let uu____7261 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7261 :: acc  in
                          (env2, uu____7258))) (env1, []) binders1
             in
          (match uu____7119 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7305 =
                 let check_what =
                   let uu____7331 = is_monadic rc_opt1  in
                   if uu____7331 then check_m else check_n  in
                 let uu____7345 = check_what env2 body1  in
                 match uu____7345 with
                 | (t,s_body,u_body) ->
                     let uu____7365 =
                       let uu____7368 =
                         let uu____7369 = is_monadic rc_opt1  in
                         if uu____7369 then M t else N t  in
                       comp_of_nm uu____7368  in
                     (uu____7365, s_body, u_body)
                  in
               (match uu____7305 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____7406 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___343_7410  ->
                                           match uu___343_7410 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7411 -> false))
                                    in
                                 if uu____7406
                                 then
                                   let uu____7412 =
                                     FStar_List.filter
                                       (fun uu___344_7416  ->
                                          match uu___344_7416 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7417 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7412
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7426 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___345_7430  ->
                                         match uu___345_7430 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7431 -> false))
                                  in
                               if uu____7426
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___346_7438  ->
                                        match uu___346_7438 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7439 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7440 =
                                   let uu____7441 =
                                     let uu____7446 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7446
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7441 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____7440
                               else
                                 (let uu____7452 =
                                    let uu___363_7453 = rc  in
                                    let uu____7454 =
                                      let uu____7459 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7459
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___363_7453.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7454;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___363_7453.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7452))
                       in
                    let uu____7464 =
                      let comp1 =
                        let uu____7472 = is_monadic rc_opt1  in
                        let uu____7473 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7472 uu____7473
                         in
                      let uu____7474 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7474,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7464 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7512 =
                             let uu____7513 =
                               let uu____7532 =
                                 let uu____7535 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7535 s_rc_opt  in
                               (s_binders1, s_body1, uu____7532)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7513  in
                           mk1 uu____7512  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7555 =
                             let uu____7556 =
                               let uu____7575 =
                                 let uu____7578 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7578 u_rc_opt  in
                               (u_binders2, u_body2, uu____7575)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7556  in
                           mk1 uu____7555  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7594;_};
            FStar_Syntax_Syntax.fv_delta = uu____7595;
            FStar_Syntax_Syntax.fv_qual = uu____7596;_}
          ->
          let uu____7599 =
            let uu____7604 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7604  in
          (match uu____7599 with
           | (uu____7635,t) ->
               let uu____7637 =
                 let uu____7638 = normalize1 t  in N uu____7638  in
               (uu____7637, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7639;
             FStar_Syntax_Syntax.vars = uu____7640;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7719 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7719 with
           | (unary_op1,uu____7743) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7814;
             FStar_Syntax_Syntax.vars = uu____7815;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7911 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7911 with
           | (unary_op1,uu____7935) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8014;
             FStar_Syntax_Syntax.vars = uu____8015;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8053 = infer env a  in
          (match uu____8053 with
           | (t,s,u) ->
               let uu____8077 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8077 with
                | (head1,uu____8101) ->
                    let uu____8126 =
                      let uu____8127 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8127  in
                    let uu____8128 =
                      let uu____8129 =
                        let uu____8130 =
                          let uu____8147 =
                            let uu____8158 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8158]  in
                          (head1, uu____8147)  in
                        FStar_Syntax_Syntax.Tm_app uu____8130  in
                      mk1 uu____8129  in
                    let uu____8195 =
                      let uu____8196 =
                        let uu____8197 =
                          let uu____8214 =
                            let uu____8225 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8225]  in
                          (head1, uu____8214)  in
                        FStar_Syntax_Syntax.Tm_app uu____8197  in
                      mk1 uu____8196  in
                    (uu____8126, uu____8128, uu____8195)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8262;
             FStar_Syntax_Syntax.vars = uu____8263;_},(a1,uu____8265)::a2::[])
          ->
          let uu____8321 = infer env a1  in
          (match uu____8321 with
           | (t,s,u) ->
               let uu____8345 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8345 with
                | (head1,uu____8369) ->
                    let uu____8394 =
                      let uu____8395 =
                        let uu____8396 =
                          let uu____8413 =
                            let uu____8424 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8424; a2]  in
                          (head1, uu____8413)  in
                        FStar_Syntax_Syntax.Tm_app uu____8396  in
                      mk1 uu____8395  in
                    let uu____8469 =
                      let uu____8470 =
                        let uu____8471 =
                          let uu____8488 =
                            let uu____8499 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8499; a2]  in
                          (head1, uu____8488)  in
                        FStar_Syntax_Syntax.Tm_app uu____8471  in
                      mk1 uu____8470  in
                    (t, uu____8394, uu____8469)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8544;
             FStar_Syntax_Syntax.vars = uu____8545;_},uu____8546)
          ->
          let uu____8571 =
            let uu____8576 =
              let uu____8577 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8577
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8576)  in
          FStar_Errors.raise_error uu____8571 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8584;
             FStar_Syntax_Syntax.vars = uu____8585;_},uu____8586)
          ->
          let uu____8611 =
            let uu____8616 =
              let uu____8617 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8617
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8616)  in
          FStar_Errors.raise_error uu____8611 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8650 = check_n env head1  in
          (match uu____8650 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8684 =
                   let uu____8685 = FStar_Syntax_Subst.compress t  in
                   uu____8685.FStar_Syntax_Syntax.n  in
                 match uu____8684 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8688 -> true
                 | uu____8703 -> false  in
               let rec flatten1 t =
                 let uu____8724 =
                   let uu____8725 = FStar_Syntax_Subst.compress t  in
                   uu____8725.FStar_Syntax_Syntax.n  in
                 match uu____8724 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8744);
                                FStar_Syntax_Syntax.pos = uu____8745;
                                FStar_Syntax_Syntax.vars = uu____8746;_})
                     when is_arrow t1 ->
                     let uu____8775 = flatten1 t1  in
                     (match uu____8775 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8875,uu____8876)
                     -> flatten1 e1
                 | uu____8917 ->
                     let uu____8918 =
                       let uu____8923 =
                         let uu____8924 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____8924
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____8923)  in
                     FStar_Errors.raise_err uu____8918
                  in
               let uu____8939 = flatten1 t_head  in
               (match uu____8939 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9013 =
                          let uu____9018 =
                            let uu____9019 = FStar_Util.string_of_int n1  in
                            let uu____9026 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9037 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9019 uu____9026 uu____9037
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9018)
                           in
                        FStar_Errors.raise_err uu____9013)
                     else ();
                     (let uu____9045 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9045 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9118 args1 =
                            match uu____9118 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9218 =
                                       let uu____9219 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____9219.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____9218
                                 | (binders3,[]) ->
                                     let uu____9257 =
                                       let uu____9258 =
                                         let uu____9261 =
                                           let uu____9262 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9262
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9261
                                          in
                                       uu____9258.FStar_Syntax_Syntax.n  in
                                     (match uu____9257 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9295 =
                                            let uu____9296 =
                                              let uu____9297 =
                                                let uu____9312 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9312)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9297
                                               in
                                            mk1 uu____9296  in
                                          N uu____9295
                                      | uu____9325 -> failwith "wat?")
                                 | ([],uu____9326::uu____9327) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9379)::binders3,(arg,uu____9382)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9469 = FStar_List.splitAt n' binders1  in
                          (match uu____9469 with
                           | (binders2,uu____9507) ->
                               let uu____9540 =
                                 let uu____9565 =
                                   FStar_List.map2
                                     (fun uu____9631  ->
                                        fun uu____9632  ->
                                          match (uu____9631, uu____9632) with
                                          | ((bv,uu____9682),(arg,q)) ->
                                              let uu____9711 =
                                                let uu____9712 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9712.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9711 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9735 ->
                                                   let uu____9736 =
                                                     let uu____9743 =
                                                       star_type' env arg  in
                                                     (uu____9743, q)  in
                                                   (uu____9736, [(arg, q)])
                                               | uu____9782 ->
                                                   let uu____9783 =
                                                     check_n env arg  in
                                                   (match uu____9783 with
                                                    | (uu____9810,s_arg,u_arg)
                                                        ->
                                                        let uu____9825 =
                                                          let uu____9836 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9836
                                                          then
                                                            let uu____9847 =
                                                              let uu____9856
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9856, q)
                                                               in
                                                            [uu____9847;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9825))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9565  in
                               (match uu____9540 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10017 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10030 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10017, uu____10030)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10096) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10106) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10112,uu____10113) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10155 =
            let uu____10156 = env.tc_const c  in N uu____10156  in
          (uu____10155, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10163 ->
          let uu____10176 =
            let uu____10177 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10177  in
          failwith uu____10176
      | FStar_Syntax_Syntax.Tm_type uu____10184 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10191 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10212 ->
          let uu____10219 =
            let uu____10220 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10220  in
          failwith uu____10219
      | FStar_Syntax_Syntax.Tm_uvar uu____10227 ->
          let uu____10240 =
            let uu____10241 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10241  in
          failwith uu____10240
      | FStar_Syntax_Syntax.Tm_delayed uu____10248 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10277 =
            let uu____10278 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10278  in
          failwith uu____10277

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____10325 = check_n env e0  in
          match uu____10325 with
          | (uu____10338,s_e0,u_e0) ->
              let uu____10353 =
                let uu____10386 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10455 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10455 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___364_10501 = env  in
                             let uu____10502 =
                               let uu____10503 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____10503
                                in
                             {
                               env = uu____10502;
                               subst = (uu___364_10501.subst);
                               tc_const = (uu___364_10501.tc_const)
                             }  in
                           let uu____10506 = f env1 body  in
                           (match uu____10506 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10602 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10386  in
              (match uu____10353 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10722 = FStar_List.hd nms  in
                     match uu____10722 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___347_10730  ->
                          match uu___347_10730 with
                          | M uu____10731 -> true
                          | uu____10732 -> false) nms
                      in
                   let uu____10733 =
                     let uu____10774 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10876  ->
                              match uu____10876 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11093 =
                                         check env original_body (M t2)  in
                                       (match uu____11093 with
                                        | (uu____11134,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11189,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10774  in
                   (match uu____10733 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____11389  ->
                                 match uu____11389 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11440 =
                                         let uu____11441 =
                                           let uu____11458 =
                                             let uu____11469 =
                                               let uu____11478 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11481 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11478, uu____11481)  in
                                             [uu____11469]  in
                                           (s_body, uu____11458)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11441
                                          in
                                       mk1 uu____11440  in
                                     (pat, guard, s_body1)) s_branches
                             in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1
                             in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches
                             in
                          let s_e =
                            let uu____11617 =
                              let uu____11618 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11618]  in
                            let uu____11637 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11617 uu____11637
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11661 =
                              let uu____11670 =
                                let uu____11677 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11677
                                 in
                              [uu____11670]  in
                            let uu____11696 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11661 uu____11696
                             in
                          let uu____11699 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11738 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11699, uu____11738)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches
                              in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches
                              in
                           let t1_star = t1  in
                           let uu____11851 =
                             let uu____11852 =
                               let uu____11853 =
                                 let uu____11880 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11880,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11853
                                in
                             mk1 uu____11852  in
                           let uu____11939 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11851, uu____11939))))

and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
                 FStar_Pervasives_Native.tuple3)
            ->
            (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos
               in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____12004 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12004]  in
            let uu____12023 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12023 with
            | (x_binders1,e21) ->
                let uu____12056 = infer env e1  in
                (match uu____12056 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12081 = is_C t1  in
                       if uu____12081
                       then
                         let uu___365_12082 = binding  in
                         let uu____12083 =
                           let uu____12086 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12086  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___365_12082.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___365_12082.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12083;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___365_12082.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___365_12082.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___365_12082.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___365_12082.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___366_12089 = env  in
                       let uu____12090 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___367_12092 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___367_12092.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___367_12092.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____12090;
                         subst = (uu___366_12089.subst);
                         tc_const = (uu___366_12089.tc_const)
                       }  in
                     let uu____12093 = proceed env1 e21  in
                     (match uu____12093 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___368_12118 = binding  in
                            let uu____12119 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___368_12118.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___368_12118.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12119;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___368_12118.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___368_12118.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___368_12118.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___368_12118.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12122 =
                            let uu____12123 =
                              let uu____12124 =
                                let uu____12137 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___369_12151 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___369_12151.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___369_12151.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___369_12151.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___369_12151.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___369_12151.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___369_12151.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12137)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12124  in
                            mk1 uu____12123  in
                          let uu____12152 =
                            let uu____12153 =
                              let uu____12154 =
                                let uu____12167 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___370_12181 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___370_12181.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___370_12181.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___370_12181.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___370_12181.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___370_12181.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___370_12181.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12167)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12154  in
                            mk1 uu____12153  in
                          (nm_rec, uu____12122, uu____12152))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___371_12194 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___371_12194.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___371_12194.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___371_12194.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___371_12194.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___371_12194.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___372_12196 = env  in
                       let uu____12197 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___373_12199 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___373_12199.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___373_12199.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____12197;
                         subst = (uu___372_12196.subst);
                         tc_const = (uu___372_12196.tc_const)
                       }  in
                     let uu____12200 = ensure_m env1 e21  in
                     (match uu____12200 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12235 =
                              let uu____12236 =
                                let uu____12253 =
                                  let uu____12264 =
                                    let uu____12273 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12276 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12273, uu____12276)  in
                                  [uu____12264]  in
                                (s_e2, uu____12253)  in
                              FStar_Syntax_Syntax.Tm_app uu____12236  in
                            mk1 uu____12235  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12317 =
                              let uu____12318 =
                                let uu____12335 =
                                  let uu____12346 =
                                    let uu____12355 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12355)  in
                                  [uu____12346]  in
                                (s_e1, uu____12335)  in
                              FStar_Syntax_Syntax.Tm_app uu____12318  in
                            mk1 uu____12317  in
                          let uu____12390 =
                            let uu____12391 =
                              let uu____12392 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12392]  in
                            FStar_Syntax_Util.abs uu____12391 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12411 =
                            let uu____12412 =
                              let uu____12413 =
                                let uu____12426 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___374_12440 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___374_12440.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___374_12440.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___374_12440.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___374_12440.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___374_12440.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___374_12440.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12426)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12413  in
                            mk1 uu____12412  in
                          ((M t2), uu____12390, uu____12411)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12450 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12450  in
      let uu____12451 = check env e mn  in
      match uu____12451 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12475 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12497 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12497  in
      let uu____12498 = check env e mn  in
      match uu____12498 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12522 -> failwith "[check_m]: impossible"

and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      {
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.monadic_lid;
        FStar_Syntax_Syntax.result_typ = t;
        FStar_Syntax_Syntax.effect_args = [];
        FStar_Syntax_Syntax.flags =
          [FStar_Syntax_Syntax.CPS; FStar_Syntax_Syntax.TOTAL]
      }

and (type_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun t  -> FStar_Syntax_Util.comp_result t

and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____12554 =
           let uu____12555 = is_C c  in Prims.op_Negation uu____12555  in
         if uu____12554 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12565 =
           let uu____12566 = FStar_Syntax_Subst.compress c  in
           uu____12566.FStar_Syntax_Syntax.n  in
         match uu____12565 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12595 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12595 with
              | (wp_head,wp_args) ->
                  ((let uu____12639 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12657 =
                           let uu____12658 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12658
                            in
                         Prims.op_Negation uu____12657)
                       in
                    if uu____12639 then failwith "mismatch" else ());
                   (let uu____12668 =
                      let uu____12669 =
                        let uu____12686 =
                          FStar_List.map2
                            (fun uu____12718  ->
                               fun uu____12719  ->
                                 match (uu____12718, uu____12719) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12758 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12758
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____12761 =
                                           let uu____12766 =
                                             let uu____12767 =
                                               print_implicit q  in
                                             let uu____12768 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12767 uu____12768
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12766)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12761)
                                      else ();
                                      (let uu____12770 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12770, q)))) args wp_args
                           in
                        (head1, uu____12686)  in
                      FStar_Syntax_Syntax.Tm_app uu____12669  in
                    mk1 uu____12668)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12814 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12814 with
              | (binders_orig,comp1) ->
                  let uu____12841 =
                    let uu____12858 =
                      FStar_List.map
                        (fun uu____12898  ->
                           match uu____12898 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12926 = is_C h  in
                               if uu____12926
                               then
                                 let w' =
                                   let uu____12940 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12940
                                    in
                                 let uu____12941 =
                                   let uu____12950 =
                                     let uu____12959 =
                                       let uu____12966 =
                                         let uu____12967 =
                                           let uu____12968 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12968  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12967
                                          in
                                       (uu____12966, q)  in
                                     [uu____12959]  in
                                   (w', q) :: uu____12950  in
                                 (w', uu____12941)
                               else
                                 (let x =
                                    let uu____13001 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13001
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12858  in
                  (match uu____12841 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13074 =
                           let uu____13077 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13077
                            in
                         FStar_Syntax_Subst.subst_comp uu____13074 comp1  in
                       let app =
                         let uu____13081 =
                           let uu____13082 =
                             let uu____13099 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13118 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13119 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13118, uu____13119)) bvs
                                in
                             (wp, uu____13099)  in
                           FStar_Syntax_Syntax.Tm_app uu____13082  in
                         mk1 uu____13081  in
                       let comp3 =
                         let uu____13133 = type_of_comp comp2  in
                         let uu____13134 = is_monadic_comp comp2  in
                         trans_G env uu____13133 uu____13134 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13136,uu____13137) ->
             trans_F_ env e wp
         | uu____13178 -> failwith "impossible trans_F_")

and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____13183 =
              let uu____13184 = star_type' env h  in
              let uu____13187 =
                let uu____13198 =
                  let uu____13207 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13207)  in
                [uu____13198]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13184;
                FStar_Syntax_Syntax.effect_args = uu____13187;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13183
          else
            (let uu____13231 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13231)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____13250 = n env.env t  in star_type' env uu____13250
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____13269 = n env.env t  in check_n env uu____13269
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13285 = n env.env c  in
        let uu____13286 = n env.env wp  in
        trans_F_ env uu____13285 uu____13286
  