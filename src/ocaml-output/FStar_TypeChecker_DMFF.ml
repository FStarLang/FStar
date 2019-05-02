open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tcenv
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> subst1
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { tcenv = env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
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
              let uu___28_129 = a  in
              let uu____130 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___28_129.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___28_129.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____130
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____143 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____143
             then
               (d "Elaborating extra WP combinators";
                (let uu____149 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____149))
             else ());
            (let rec collect_binders t =
               let uu____168 =
                 let uu____169 =
                   let uu____172 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____172
                    in
                 uu____169.FStar_Syntax_Syntax.n  in
               match uu____168 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____207) -> t1
                     | FStar_Syntax_Syntax.GTotal (t1,uu____217) -> t1
                     | uu____226 ->
                         let uu____227 =
                           let uu____229 =
                             FStar_Syntax_Print.comp_to_string comp  in
                           Prims.op_Hat "wp_a contains non-Tot arrow: "
                             uu____229
                            in
                         failwith uu____227
                      in
                   let uu____232 = collect_binders rest  in
                   FStar_List.append bs uu____232
               | FStar_Syntax_Syntax.Tm_type uu____247 -> []
               | uu____254 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____281 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____281 FStar_Syntax_Util.name_binders
                in
             (let uu____307 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____307
              then
                let uu____311 =
                  let uu____313 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____313  in
                d uu____311
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____351 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____351 with
                | (sigelt,fv) ->
                    ((let uu____359 =
                        let uu____362 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____362
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____359);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____442  ->
                     match uu____442 with
                     | (t,b) ->
                         let uu____456 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____456))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____495 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____495))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____529 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____529)
                 in
              let uu____532 =
                let uu____549 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____574 =
                        let uu____577 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____577  in
                      FStar_Syntax_Util.arrow gamma uu____574  in
                    let uu____578 =
                      let uu____579 =
                        let uu____588 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____595 =
                          let uu____604 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____604]  in
                        uu____588 :: uu____595  in
                      FStar_List.append binders uu____579  in
                    FStar_Syntax_Util.abs uu____578 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____635 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____636 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____635, uu____636)  in
                match uu____549 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____678 =
                        let uu____679 =
                          let uu____696 =
                            let uu____707 =
                              FStar_List.map
                                (fun uu____729  ->
                                   match uu____729 with
                                   | (bv,uu____741) ->
                                       let uu____746 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____747 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____746, uu____747)) binders
                               in
                            let uu____749 =
                              let uu____756 =
                                let uu____761 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____762 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____761, uu____762)  in
                              let uu____764 =
                                let uu____771 =
                                  let uu____776 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____776)  in
                                [uu____771]  in
                              uu____756 :: uu____764  in
                            FStar_List.append uu____707 uu____749  in
                          (fv, uu____696)  in
                        FStar_Syntax_Syntax.Tm_app uu____679  in
                      mk1 uu____678  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____532 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____849 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____849
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
                    let uu____911 = mk_lid "pure"  in
                    register env1 uu____911 c_pure  in
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
                      let uu____921 =
                        let uu____922 =
                          let uu____923 =
                            let uu____932 =
                              let uu____939 =
                                let uu____940 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____940
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____939  in
                            [uu____932]  in
                          let uu____953 =
                            let uu____956 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____956  in
                          FStar_Syntax_Util.arrow uu____923 uu____953  in
                        mk_gctx uu____922  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____921
                       in
                    let r =
                      let uu____959 =
                        let uu____960 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____960  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____959
                       in
                    let ret1 =
                      let uu____965 =
                        let uu____966 =
                          let uu____969 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____969  in
                        FStar_Syntax_Util.residual_tot uu____966  in
                      FStar_Pervasives_Native.Some uu____965  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____979 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____982 =
                          let uu____993 =
                            let uu____996 =
                              let uu____997 =
                                let uu____998 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____998
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____997  in
                            [uu____996]  in
                          FStar_List.append gamma_as_args uu____993  in
                        FStar_Syntax_Util.mk_app uu____979 uu____982  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____1001 =
                      let uu____1002 = mk_all_implicit binders  in
                      let uu____1009 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____1002 uu____1009  in
                    FStar_Syntax_Util.abs uu____1001 outer_body ret1  in
                  let c_app1 =
                    let uu____1061 = mk_lid "app"  in
                    register env1 uu____1061 c_app  in
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
                      let uu____1073 =
                        let uu____1082 =
                          let uu____1089 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1089  in
                        [uu____1082]  in
                      let uu____1102 =
                        let uu____1105 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1105  in
                      FStar_Syntax_Util.arrow uu____1073 uu____1102  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1109 =
                        let uu____1110 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1110  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1109
                       in
                    let ret1 =
                      let uu____1115 =
                        let uu____1116 =
                          let uu____1119 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1119  in
                        FStar_Syntax_Util.residual_tot uu____1116  in
                      FStar_Pervasives_Native.Some uu____1115  in
                    let uu____1120 =
                      let uu____1121 = mk_all_implicit binders  in
                      let uu____1128 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1121 uu____1128  in
                    let uu____1179 =
                      let uu____1182 =
                        let uu____1193 =
                          let uu____1196 =
                            let uu____1197 =
                              let uu____1208 =
                                let uu____1211 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1211]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1208
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1197  in
                          let uu____1220 =
                            let uu____1223 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1223]  in
                          uu____1196 :: uu____1220  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1193
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1182  in
                    FStar_Syntax_Util.abs uu____1120 uu____1179 ret1  in
                  let c_lift11 =
                    let uu____1233 = mk_lid "lift1"  in
                    register env1 uu____1233 c_lift1  in
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
                      let uu____1247 =
                        let uu____1256 =
                          let uu____1263 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1263  in
                        let uu____1264 =
                          let uu____1273 =
                            let uu____1280 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1280  in
                          [uu____1273]  in
                        uu____1256 :: uu____1264  in
                      let uu____1299 =
                        let uu____1302 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1302  in
                      FStar_Syntax_Util.arrow uu____1247 uu____1299  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1306 =
                        let uu____1307 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1307  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1306
                       in
                    let a2 =
                      let uu____1310 =
                        let uu____1311 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1311  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1310
                       in
                    let ret1 =
                      let uu____1316 =
                        let uu____1317 =
                          let uu____1320 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1320  in
                        FStar_Syntax_Util.residual_tot uu____1317  in
                      FStar_Pervasives_Native.Some uu____1316  in
                    let uu____1321 =
                      let uu____1322 = mk_all_implicit binders  in
                      let uu____1329 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1322 uu____1329  in
                    let uu____1394 =
                      let uu____1397 =
                        let uu____1408 =
                          let uu____1411 =
                            let uu____1412 =
                              let uu____1423 =
                                let uu____1426 =
                                  let uu____1427 =
                                    let uu____1438 =
                                      let uu____1441 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1441]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1438
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1427
                                   in
                                let uu____1450 =
                                  let uu____1453 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1453]  in
                                uu____1426 :: uu____1450  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1423
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1412  in
                          let uu____1462 =
                            let uu____1465 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1465]  in
                          uu____1411 :: uu____1462  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1408
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1397  in
                    FStar_Syntax_Util.abs uu____1321 uu____1394 ret1  in
                  let c_lift21 =
                    let uu____1475 = mk_lid "lift2"  in
                    register env1 uu____1475 c_lift2  in
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
                      let uu____1487 =
                        let uu____1496 =
                          let uu____1503 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1503  in
                        [uu____1496]  in
                      let uu____1516 =
                        let uu____1519 =
                          let uu____1520 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1520  in
                        FStar_Syntax_Syntax.mk_Total uu____1519  in
                      FStar_Syntax_Util.arrow uu____1487 uu____1516  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1526 =
                        let uu____1527 =
                          let uu____1530 =
                            let uu____1531 =
                              let uu____1540 =
                                let uu____1547 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1547
                                 in
                              [uu____1540]  in
                            let uu____1560 =
                              let uu____1563 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1563  in
                            FStar_Syntax_Util.arrow uu____1531 uu____1560  in
                          mk_ctx uu____1530  in
                        FStar_Syntax_Util.residual_tot uu____1527  in
                      FStar_Pervasives_Native.Some uu____1526  in
                    let e1 =
                      let uu____1565 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1565
                       in
                    let body =
                      let uu____1570 =
                        let uu____1571 =
                          let uu____1580 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1580]  in
                        FStar_List.append gamma uu____1571  in
                      let uu____1605 =
                        let uu____1608 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1611 =
                          let uu____1622 =
                            let uu____1623 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1623  in
                          let uu____1624 = args_of_binders1 gamma  in
                          uu____1622 :: uu____1624  in
                        FStar_Syntax_Util.mk_app uu____1608 uu____1611  in
                      FStar_Syntax_Util.abs uu____1570 uu____1605 ret1  in
                    let uu____1627 =
                      let uu____1628 = mk_all_implicit binders  in
                      let uu____1635 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1628 uu____1635  in
                    FStar_Syntax_Util.abs uu____1627 body ret1  in
                  let c_push1 =
                    let uu____1680 = mk_lid "push"  in
                    register env1 uu____1680 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1707 =
                        let uu____1708 =
                          let uu____1725 = args_of_binders1 binders  in
                          (c, uu____1725)  in
                        FStar_Syntax_Syntax.Tm_app uu____1708  in
                      mk1 uu____1707
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1754 =
                        let uu____1755 =
                          let uu____1764 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1771 =
                            let uu____1780 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1780]  in
                          uu____1764 :: uu____1771  in
                        let uu____1805 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1755 uu____1805  in
                      FStar_Syntax_Syntax.mk_Total uu____1754  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1810 =
                      let uu____1811 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1811  in
                    let uu____1826 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1831 =
                        let uu____1834 =
                          let uu____1845 =
                            let uu____1848 =
                              let uu____1849 =
                                let uu____1860 =
                                  let uu____1869 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1869  in
                                [uu____1860]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1849  in
                            [uu____1848]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1845
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1834  in
                      FStar_Syntax_Util.ascribe uu____1831
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1810 uu____1826
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1913 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1913 wp_if_then_else  in
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
                      let uu____1930 =
                        let uu____1941 =
                          let uu____1944 =
                            let uu____1945 =
                              let uu____1956 =
                                let uu____1959 =
                                  let uu____1960 =
                                    let uu____1971 =
                                      let uu____1980 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1980
                                       in
                                    [uu____1971]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1960
                                   in
                                [uu____1959]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1956
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1945  in
                          let uu____2005 =
                            let uu____2008 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2008]  in
                          uu____1944 :: uu____2005  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1941
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1930  in
                    let uu____2017 =
                      let uu____2018 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2018  in
                    FStar_Syntax_Util.abs uu____2017 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____2034 = mk_lid "wp_assert"  in
                    register env1 uu____2034 wp_assert  in
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
                      let uu____2051 =
                        let uu____2062 =
                          let uu____2065 =
                            let uu____2066 =
                              let uu____2077 =
                                let uu____2080 =
                                  let uu____2081 =
                                    let uu____2092 =
                                      let uu____2101 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2101
                                       in
                                    [uu____2092]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____2081
                                   in
                                [uu____2080]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____2077
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2066  in
                          let uu____2126 =
                            let uu____2129 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2129]  in
                          uu____2065 :: uu____2126  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2062
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2051  in
                    let uu____2138 =
                      let uu____2139 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2139  in
                    FStar_Syntax_Util.abs uu____2138 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2155 = mk_lid "wp_assume"  in
                    register env1 uu____2155 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2168 =
                        let uu____2177 =
                          let uu____2184 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2184  in
                        [uu____2177]  in
                      let uu____2197 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2168 uu____2197  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2205 =
                        let uu____2216 =
                          let uu____2219 =
                            let uu____2220 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2220  in
                          let uu____2239 =
                            let uu____2242 =
                              let uu____2243 =
                                let uu____2254 =
                                  let uu____2257 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2257]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2254
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2243  in
                            [uu____2242]  in
                          uu____2219 :: uu____2239  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2216
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2205  in
                    let uu____2274 =
                      let uu____2275 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2275  in
                    FStar_Syntax_Util.abs uu____2274 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2291 = mk_lid "wp_close"  in
                    register env1 uu____2291 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2302 =
                      let uu____2303 =
                        let uu____2304 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2304
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2303  in
                    FStar_Pervasives_Native.Some uu____2302  in
                  let mk_forall1 x body =
                    let uu____2316 =
                      let uu____2323 =
                        let uu____2324 =
                          let uu____2341 =
                            let uu____2352 =
                              let uu____2361 =
                                let uu____2362 =
                                  let uu____2363 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2363]  in
                                FStar_Syntax_Util.abs uu____2362 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2361  in
                            [uu____2352]  in
                          (FStar_Syntax_Util.tforall, uu____2341)  in
                        FStar_Syntax_Syntax.Tm_app uu____2324  in
                      FStar_Syntax_Syntax.mk uu____2323  in
                    uu____2316 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2421 =
                      let uu____2422 = FStar_Syntax_Subst.compress t  in
                      uu____2422.FStar_Syntax_Syntax.n  in
                    match uu____2421 with
                    | FStar_Syntax_Syntax.Tm_type uu____2426 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2459  ->
                              match uu____2459 with
                              | (b,uu____2468) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2473 -> true  in
                  let rec is_monotonic t =
                    let uu____2486 =
                      let uu____2487 = FStar_Syntax_Subst.compress t  in
                      uu____2487.FStar_Syntax_Syntax.n  in
                    match uu____2486 with
                    | FStar_Syntax_Syntax.Tm_type uu____2491 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2524  ->
                              match uu____2524 with
                              | (b,uu____2533) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2538 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2612 =
                      let uu____2613 = FStar_Syntax_Subst.compress t1  in
                      uu____2613.FStar_Syntax_Syntax.n  in
                    match uu____2612 with
                    | FStar_Syntax_Syntax.Tm_type uu____2618 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2621);
                                      FStar_Syntax_Syntax.pos = uu____2622;
                                      FStar_Syntax_Syntax.vars = uu____2623;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2667 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2667
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2677 =
                              let uu____2680 =
                                let uu____2691 =
                                  let uu____2700 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2700  in
                                [uu____2691]  in
                              FStar_Syntax_Util.mk_app x uu____2680  in
                            let uu____2717 =
                              let uu____2720 =
                                let uu____2731 =
                                  let uu____2740 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2740  in
                                [uu____2731]  in
                              FStar_Syntax_Util.mk_app y uu____2720  in
                            mk_rel1 b uu____2677 uu____2717  in
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
                             let uu____2764 =
                               let uu____2767 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2770 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2767 uu____2770  in
                             let uu____2773 =
                               let uu____2776 =
                                 let uu____2779 =
                                   let uu____2790 =
                                     let uu____2799 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2799
                                      in
                                   [uu____2790]  in
                                 FStar_Syntax_Util.mk_app x uu____2779  in
                               let uu____2816 =
                                 let uu____2819 =
                                   let uu____2830 =
                                     let uu____2839 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2839
                                      in
                                   [uu____2830]  in
                                 FStar_Syntax_Util.mk_app y uu____2819  in
                               mk_rel1 b uu____2776 uu____2816  in
                             FStar_Syntax_Util.mk_imp uu____2764 uu____2773
                              in
                           let uu____2856 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2856)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2859);
                                      FStar_Syntax_Syntax.pos = uu____2860;
                                      FStar_Syntax_Syntax.vars = uu____2861;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2905 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2905
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2915 =
                              let uu____2918 =
                                let uu____2929 =
                                  let uu____2938 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2938  in
                                [uu____2929]  in
                              FStar_Syntax_Util.mk_app x uu____2918  in
                            let uu____2955 =
                              let uu____2958 =
                                let uu____2969 =
                                  let uu____2978 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2978  in
                                [uu____2969]  in
                              FStar_Syntax_Util.mk_app y uu____2958  in
                            mk_rel1 b uu____2915 uu____2955  in
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
                             let uu____3002 =
                               let uu____3005 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____3008 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____3005 uu____3008  in
                             let uu____3011 =
                               let uu____3014 =
                                 let uu____3017 =
                                   let uu____3028 =
                                     let uu____3037 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____3037
                                      in
                                   [uu____3028]  in
                                 FStar_Syntax_Util.mk_app x uu____3017  in
                               let uu____3054 =
                                 let uu____3057 =
                                   let uu____3068 =
                                     let uu____3077 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____3077
                                      in
                                   [uu____3068]  in
                                 FStar_Syntax_Util.mk_app y uu____3057  in
                               mk_rel1 b uu____3014 uu____3054  in
                             FStar_Syntax_Util.mk_imp uu____3002 uu____3011
                              in
                           let uu____3094 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____3094)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___245_3133 = t1  in
                          let uu____3134 =
                            let uu____3135 =
                              let uu____3150 =
                                let uu____3153 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3153  in
                              ([binder], uu____3150)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3135  in
                          {
                            FStar_Syntax_Syntax.n = uu____3134;
                            FStar_Syntax_Syntax.pos =
                              (uu___245_3133.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___245_3133.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3176 ->
                        failwith "unhandled arrow"
                    | uu____3194 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____3231 =
                        let uu____3232 = FStar_Syntax_Subst.compress t1  in
                        uu____3232.FStar_Syntax_Syntax.n  in
                      match uu____3231 with
                      | FStar_Syntax_Syntax.Tm_type uu____3235 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3262 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3262
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3283 =
                                let uu____3284 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3284 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3283
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3314 =
                            let uu____3325 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3343  ->
                                     match uu____3343 with
                                     | (t2,q) ->
                                         let uu____3363 = project i x  in
                                         let uu____3366 = project i y  in
                                         mk_stronger t2 uu____3363 uu____3366)
                                args
                               in
                            match uu____3325 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3314 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3420);
                                      FStar_Syntax_Syntax.pos = uu____3421;
                                      FStar_Syntax_Syntax.vars = uu____3422;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3466  ->
                                   match uu____3466 with
                                   | (bv,q) ->
                                       let uu____3480 =
                                         let uu____3482 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3482  in
                                       FStar_Syntax_Syntax.gen_bv uu____3480
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3491 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3491) bvs
                             in
                          let body =
                            let uu____3493 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3496 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3493 uu____3496  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3505);
                                      FStar_Syntax_Syntax.pos = uu____3506;
                                      FStar_Syntax_Syntax.vars = uu____3507;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3551  ->
                                   match uu____3551 with
                                   | (bv,q) ->
                                       let uu____3565 =
                                         let uu____3567 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3567  in
                                       FStar_Syntax_Syntax.gen_bv uu____3565
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3576 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3576) bvs
                             in
                          let body =
                            let uu____3578 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3581 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3578 uu____3581  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3588 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3591 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3594 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3597 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3591 uu____3594 uu____3597  in
                    let uu____3600 =
                      let uu____3601 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3601  in
                    FStar_Syntax_Util.abs uu____3600 body ret_tot_type  in
                  let stronger1 =
                    let uu____3643 = mk_lid "stronger"  in
                    register env1 uu____3643 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let mrelation_from_interp interp =
                    let repr_a =
                      let uu____3657 =
                        let uu____3668 =
                          let uu____3677 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          FStar_Syntax_Syntax.as_arg uu____3677  in
                        [uu____3668]  in
                      FStar_Syntax_Util.mk_app
                        (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                        uu____3657
                       in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        (FStar_Pervasives_Native.Some
                           (interp.FStar_Syntax_Syntax.pos)) repr_a
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        (FStar_Pervasives_Native.Some
                           (interp.FStar_Syntax_Syntax.pos)) wp_a1
                       in
                    let body =
                      let uu____3701 =
                        let uu____3712 =
                          let uu____3721 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          FStar_Syntax_Syntax.as_arg uu____3721  in
                        let uu____3722 =
                          let uu____3733 =
                            let uu____3742 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            FStar_Syntax_Syntax.as_arg uu____3742  in
                          let uu____3743 =
                            let uu____3754 =
                              let uu____3763 =
                                let uu____3764 =
                                  let uu____3775 =
                                    let uu____3784 =
                                      FStar_Syntax_Syntax.bv_to_name a1  in
                                    FStar_Syntax_Syntax.iarg uu____3784  in
                                  let uu____3785 =
                                    let uu____3796 =
                                      let uu____3805 =
                                        FStar_Syntax_Syntax.bv_to_name c  in
                                      FStar_Syntax_Syntax.as_arg uu____3805
                                       in
                                    [uu____3796]  in
                                  uu____3775 :: uu____3785  in
                                FStar_Syntax_Util.mk_app interp uu____3764
                                 in
                              FStar_Syntax_Syntax.as_arg uu____3763  in
                            [uu____3754]  in
                          uu____3733 :: uu____3743  in
                        uu____3712 :: uu____3722  in
                      FStar_Syntax_Util.mk_app stronger2 uu____3701  in
                    let abs1 =
                      let uu____3865 =
                        let uu____3866 =
                          let uu____3875 =
                            FStar_Syntax_Syntax.mk_implicit_binder a1  in
                          let uu____3882 =
                            let uu____3891 = FStar_Syntax_Syntax.mk_binder c
                               in
                            let uu____3898 =
                              let uu____3907 =
                                FStar_Syntax_Syntax.mk_binder wp  in
                              [uu____3907]  in
                            uu____3891 :: uu____3898  in
                          uu____3875 :: uu____3882  in
                        FStar_List.append binders uu____3866  in
                      FStar_Syntax_Util.abs uu____3865 body ret_tot_type  in
                    abs1  in
                  let mrelation =
                    match ((ed.FStar_Syntax_Syntax.interp),
                            (ed.FStar_Syntax_Syntax.mrelation))
                    with
                    | (uu____3953,FStar_Pervasives_Native.Some t) ->
                        FStar_Pervasives_Native.Some
                          (FStar_Pervasives_Native.snd t)
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        FStar_Pervasives_Native.None
                    | (FStar_Pervasives_Native.Some
                       i,FStar_Pervasives_Native.None ) ->
                        let uu____3974 =
                          mrelation_from_interp
                            (FStar_Pervasives_Native.snd i)
                           in
                        FStar_Pervasives_Native.Some uu____3974
                     in
                  let mrelation1 =
                    let uu____3984 =
                      let uu____3991 = mk_lid "mrelation"  in
                      register env1 uu____3991  in
                    FStar_Util.map_opt mrelation uu____3984  in
                  let mrelation2 =
                    FStar_Util.map_opt mrelation1 mk_generic_app  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____4003 = FStar_Util.prefix gamma  in
                    match uu____4003 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____4069 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____4069
                             in
                          let uu____4074 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____4074 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____4084 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____4084  in
                              let guard_free1 =
                                let uu____4096 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____4096  in
                              let pat =
                                let uu____4100 =
                                  let uu____4111 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____4111]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____4100
                                 in
                              let pattern_guarded_body =
                                let uu____4139 =
                                  let uu____4140 =
                                    let uu____4147 =
                                      let uu____4148 =
                                        let uu____4161 =
                                          let uu____4172 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____4172]  in
                                        [uu____4161]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____4148
                                       in
                                    (body, uu____4147)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____4140  in
                                mk1 uu____4139  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____4219 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____4228 =
                            let uu____4231 =
                              let uu____4232 =
                                let uu____4235 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____4238 =
                                  let uu____4249 = args_of_binders1 wp_args
                                     in
                                  let uu____4252 =
                                    let uu____4255 =
                                      let uu____4256 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____4256
                                       in
                                    [uu____4255]  in
                                  FStar_List.append uu____4249 uu____4252  in
                                FStar_Syntax_Util.mk_app uu____4235
                                  uu____4238
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____4232  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____4231
                             in
                          FStar_Syntax_Util.abs gamma uu____4228
                            ret_gtot_type
                           in
                        let uu____4257 =
                          let uu____4258 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____4258  in
                        FStar_Syntax_Util.abs uu____4257 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____4274 = mk_lid "ite_wp"  in
                    register env1 uu____4274 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____4282 = FStar_Util.prefix gamma  in
                    match uu____4282 with
                    | (wp_args,post) ->
                        let uu____4337 =
                          FStar_Syntax_Util.arrow_formals_comp
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        (match uu____4337 with
                         | (bs,uu____4353) ->
                             let bs1 =
                               FStar_List.map
                                 FStar_Syntax_Syntax.freshen_binder bs
                                in
                             let args =
                               FStar_List.map
                                 (fun uu____4416  ->
                                    match uu____4416 with
                                    | (bv,q) ->
                                        let uu____4435 =
                                          FStar_Syntax_Syntax.bv_to_name bv
                                           in
                                        (uu____4435, q)) bs1
                                in
                             let body =
                               let uu____4439 =
                                 let uu____4440 =
                                   FStar_All.pipe_left
                                     FStar_Syntax_Syntax.bv_to_name
                                     (FStar_Pervasives_Native.fst post)
                                    in
                                 FStar_Syntax_Util.mk_app uu____4440 args  in
                               FStar_Syntax_Util.close_forall_no_univs bs1
                                 uu____4439
                                in
                             let uu____4447 =
                               let uu____4448 =
                                 let uu____4457 =
                                   FStar_Syntax_Syntax.binders_of_list [a1]
                                    in
                                 FStar_List.append uu____4457 gamma  in
                               FStar_List.append binders uu____4448  in
                             FStar_Syntax_Util.abs uu____4447 body
                               ret_gtot_type)
                     in
                  let null_wp1 =
                    let uu____4479 = mk_lid "null_wp"  in
                    register env1 uu____4479 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____4492 =
                        let uu____4503 =
                          let uu____4506 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4507 =
                            let uu____4510 =
                              let uu____4511 =
                                let uu____4522 =
                                  let uu____4531 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4531  in
                                [uu____4522]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4511
                               in
                            let uu____4548 =
                              let uu____4551 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4551]  in
                            uu____4510 :: uu____4548  in
                          uu____4506 :: uu____4507  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4503
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____4492  in
                    let uu____4560 =
                      let uu____4561 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4561  in
                    FStar_Syntax_Util.abs uu____4560 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4577 = mk_lid "wp_trivial"  in
                    register env1 uu____4577 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4583 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4583
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4595 =
                      let uu____4596 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4596  in
                    let uu____4622 =
                      let uu___380_4623 = ed  in
                      let uu____4624 =
                        let uu____4625 = c wp_if_then_else2  in
                        ([], uu____4625)  in
                      let uu____4632 =
                        let uu____4633 = c ite_wp2  in ([], uu____4633)  in
                      let uu____4640 =
                        let uu____4641 = c stronger2  in ([], uu____4641)  in
                      let uu____4648 =
                        let uu____4649 = c wp_close2  in ([], uu____4649)  in
                      let uu____4656 =
                        let uu____4657 = c wp_assert2  in ([], uu____4657)
                         in
                      let uu____4664 =
                        let uu____4665 = c wp_assume2  in ([], uu____4665)
                         in
                      let uu____4672 =
                        let uu____4673 = c null_wp2  in ([], uu____4673)  in
                      let uu____4680 =
                        let uu____4681 = c wp_trivial2  in ([], uu____4681)
                         in
                      let uu____4688 =
                        FStar_Util.map_opt mrelation2
                          (fun t  ->
                             let uu____4700 = c t  in ([], uu____4700))
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___380_4623.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___380_4623.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___380_4623.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___380_4623.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.spec =
                          (uu___380_4623.FStar_Syntax_Syntax.spec);
                        FStar_Syntax_Syntax.signature =
                          (uu___380_4623.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.if_then_else = uu____4624;
                        FStar_Syntax_Syntax.ite_wp = uu____4632;
                        FStar_Syntax_Syntax.stronger = uu____4640;
                        FStar_Syntax_Syntax.close_wp = uu____4648;
                        FStar_Syntax_Syntax.assert_p = uu____4656;
                        FStar_Syntax_Syntax.assume_p = uu____4664;
                        FStar_Syntax_Syntax.null_wp = uu____4672;
                        FStar_Syntax_Syntax.trivial = uu____4680;
                        FStar_Syntax_Syntax.repr =
                          (uu___380_4623.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.elaborated =
                          (uu___380_4623.FStar_Syntax_Syntax.elaborated);
                        FStar_Syntax_Syntax.spec_dm4f =
                          (uu___380_4623.FStar_Syntax_Syntax.spec_dm4f);
                        FStar_Syntax_Syntax.interp =
                          (uu___380_4623.FStar_Syntax_Syntax.interp);
                        FStar_Syntax_Syntax.mrelation = uu____4688;
                        FStar_Syntax_Syntax.actions =
                          (uu___380_4623.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___380_4623.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4595, uu____4622)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___386_4720 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___386_4720.subst);
        tc_const = (uu___386_4720.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4741 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4760 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4780) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4794  ->
                match uu___0_4794 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4797 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4799 ->
        let uu____4800 =
          let uu____4806 =
            let uu____4808 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4808
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4806)  in
        FStar_Errors.raise_error uu____4800 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4818  ->
    match uu___1_4818 with
    | N t ->
        let uu____4821 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4821
    | M t ->
        let uu____4825 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4825
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4834,c) -> nm_of_comp c
    | uu____4856 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4869 = nm_of_comp c  in
    match uu____4869 with | M uu____4871 -> true | N uu____4873 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4884 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4900 =
        let uu____4909 =
          let uu____4916 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4916  in
        [uu____4909]  in
      let uu____4935 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4900 uu____4935  in
    let uu____4938 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4938
  
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
        let uu____4980 =
          let uu____4981 =
            let uu____4996 =
              let uu____5005 =
                let uu____5012 =
                  let uu____5013 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____5013  in
                let uu____5014 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____5012, uu____5014)  in
              [uu____5005]  in
            let uu____5032 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4996, uu____5032)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4981  in
        mk1 uu____4980

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____5072) ->
          let binders1 =
            FStar_List.map
              (fun uu____5118  ->
                 match uu____5118 with
                 | (bv,aqual) ->
                     let uu____5137 =
                       let uu___436_5138 = bv  in
                       let uu____5139 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___436_5138.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___436_5138.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____5139
                       }  in
                     (uu____5137, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____5144,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____5146);
                             FStar_Syntax_Syntax.pos = uu____5147;
                             FStar_Syntax_Syntax.vars = uu____5148;_})
               ->
               let uu____5177 =
                 let uu____5178 =
                   let uu____5193 =
                     let uu____5196 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____5196  in
                   (binders1, uu____5193)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____5178  in
               mk1 uu____5177
           | uu____5207 ->
               let uu____5208 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____5208 with
                | N hn ->
                    let uu____5210 =
                      let uu____5211 =
                        let uu____5226 =
                          let uu____5229 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____5229  in
                        (binders1, uu____5226)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____5211  in
                    mk1 uu____5210
                | M a ->
                    let uu____5241 =
                      let uu____5242 =
                        let uu____5257 =
                          let uu____5266 =
                            let uu____5275 =
                              let uu____5282 =
                                let uu____5283 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____5283  in
                              let uu____5284 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____5282, uu____5284)  in
                            [uu____5275]  in
                          FStar_List.append binders1 uu____5266  in
                        let uu____5308 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____5257, uu____5308)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____5242  in
                    mk1 uu____5241))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____5402 = f x  in
                    FStar_Util.string_builder_append strb uu____5402);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____5411 = f x1  in
                         FStar_Util.string_builder_append strb uu____5411))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____5415 =
              let uu____5421 =
                let uu____5423 = FStar_Syntax_Print.term_to_string t2  in
                let uu____5425 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____5423 uu____5425
                 in
              (FStar_Errors.Warning_DependencyFound, uu____5421)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____5415  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____5447 =
              let uu____5448 = FStar_Syntax_Subst.compress ty  in
              uu____5448.FStar_Syntax_Syntax.n  in
            match uu____5447 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5474 =
                  let uu____5476 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____5476  in
                if uu____5474
                then false
                else
                  (try
                     (fun uu___485_5493  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____5517 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____5517 s  in
                              let uu____5520 =
                                let uu____5522 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____5522  in
                              if uu____5520
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____5528 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____5528 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5553  ->
                                          match uu____5553 with
                                          | (bv,uu____5565) ->
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
            | uu____5593 ->
                ((let uu____5595 =
                    let uu____5601 =
                      let uu____5603 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5603
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5601)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5595);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5619 =
              let uu____5620 = FStar_Syntax_Subst.compress head2  in
              uu____5620.FStar_Syntax_Syntax.n  in
            match uu____5619 with
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
                  (let uu____5626 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5626)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5629 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5629 with
                 | ((uu____5639,ty),uu____5641) ->
                     let uu____5646 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5646
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5659 =
                         let uu____5660 = FStar_Syntax_Subst.compress res  in
                         uu____5660.FStar_Syntax_Syntax.n  in
                       (match uu____5659 with
                        | FStar_Syntax_Syntax.Tm_app uu____5664 -> true
                        | uu____5682 ->
                            ((let uu____5684 =
                                let uu____5690 =
                                  let uu____5692 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5692
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5690)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5684);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5700 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5702 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5705) ->
                is_valid_application t2
            | uu____5710 -> false  in
          let uu____5712 = is_valid_application head1  in
          if uu____5712
          then
            let uu____5715 =
              let uu____5716 =
                let uu____5733 =
                  FStar_List.map
                    (fun uu____5762  ->
                       match uu____5762 with
                       | (t2,qual) ->
                           let uu____5787 = star_type' env t2  in
                           (uu____5787, qual)) args
                   in
                (head1, uu____5733)  in
              FStar_Syntax_Syntax.Tm_app uu____5716  in
            mk1 uu____5715
          else
            (let uu____5804 =
               let uu____5810 =
                 let uu____5812 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5812
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5810)  in
             FStar_Errors.raise_err uu____5804)
      | FStar_Syntax_Syntax.Tm_bvar uu____5816 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5817 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5818 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5819 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5847 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5847 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___557_5855 = env  in
                 let uu____5856 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5856;
                   subst = (uu___557_5855.subst);
                   tc_const = (uu___557_5855.tc_const)
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
               ((let uu___572_5883 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___572_5883.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___572_5883.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5890 =
            let uu____5891 =
              let uu____5898 = star_type' env t2  in (uu____5898, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5891  in
          mk1 uu____5890
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5950 =
            let uu____5951 =
              let uu____5978 = star_type' env e  in
              let uu____5981 =
                let uu____5998 =
                  let uu____6007 = star_type' env t2  in
                  FStar_Util.Inl uu____6007  in
                (uu____5998, FStar_Pervasives_Native.None)  in
              (uu____5978, uu____5981, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5951  in
          mk1 uu____5950
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____6095 =
            let uu____6096 =
              let uu____6123 = star_type' env e  in
              let uu____6126 =
                let uu____6143 =
                  let uu____6152 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____6152  in
                (uu____6143, FStar_Pervasives_Native.None)  in
              (uu____6123, uu____6126, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____6096  in
          mk1 uu____6095
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____6193,(uu____6194,FStar_Pervasives_Native.Some uu____6195),uu____6196)
          ->
          let uu____6245 =
            let uu____6251 =
              let uu____6253 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____6253
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6251)  in
          FStar_Errors.raise_err uu____6245
      | FStar_Syntax_Syntax.Tm_refine uu____6257 ->
          let uu____6264 =
            let uu____6270 =
              let uu____6272 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____6272
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6270)  in
          FStar_Errors.raise_err uu____6264
      | FStar_Syntax_Syntax.Tm_uinst uu____6276 ->
          let uu____6283 =
            let uu____6289 =
              let uu____6291 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____6291
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6289)  in
          FStar_Errors.raise_err uu____6283
      | FStar_Syntax_Syntax.Tm_quoted uu____6295 ->
          let uu____6302 =
            let uu____6308 =
              let uu____6310 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____6310
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6308)  in
          FStar_Errors.raise_err uu____6302
      | FStar_Syntax_Syntax.Tm_constant uu____6314 ->
          let uu____6315 =
            let uu____6321 =
              let uu____6323 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____6323
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6321)  in
          FStar_Errors.raise_err uu____6315
      | FStar_Syntax_Syntax.Tm_match uu____6327 ->
          let uu____6350 =
            let uu____6356 =
              let uu____6358 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____6358
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6356)  in
          FStar_Errors.raise_err uu____6350
      | FStar_Syntax_Syntax.Tm_let uu____6362 ->
          let uu____6376 =
            let uu____6382 =
              let uu____6384 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____6384
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6382)  in
          FStar_Errors.raise_err uu____6376
      | FStar_Syntax_Syntax.Tm_uvar uu____6388 ->
          let uu____6401 =
            let uu____6407 =
              let uu____6409 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____6409
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6407)  in
          FStar_Errors.raise_err uu____6401
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6413 =
            let uu____6419 =
              let uu____6421 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____6421
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6419)  in
          FStar_Errors.raise_err uu____6413
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6426 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____6426
      | FStar_Syntax_Syntax.Tm_delayed uu____6429 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_6461  ->
    match uu___3_6461 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_6472  ->
                match uu___2_6472 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____6475 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____6485 =
      let uu____6486 = FStar_Syntax_Subst.compress t  in
      uu____6486.FStar_Syntax_Syntax.n  in
    match uu____6485 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____6518 =
            let uu____6519 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____6519  in
          is_C uu____6518  in
        if r
        then
          ((let uu____6543 =
              let uu____6545 =
                FStar_List.for_all
                  (fun uu____6556  ->
                     match uu____6556 with | (h,uu____6565) -> is_C h) args
                 in
              Prims.op_Negation uu____6545  in
            if uu____6543 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6578 =
              let uu____6580 =
                FStar_List.for_all
                  (fun uu____6592  ->
                     match uu____6592 with
                     | (h,uu____6601) ->
                         let uu____6606 = is_C h  in
                         Prims.op_Negation uu____6606) args
                 in
              Prims.op_Negation uu____6580  in
            if uu____6578 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6635 = nm_of_comp comp  in
        (match uu____6635 with
         | M t1 ->
             ((let uu____6639 = is_C t1  in
               if uu____6639 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6648) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6654) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6660,uu____6661) -> is_C t1
    | uu____6702 -> false
  
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
          let uu____6738 =
            let uu____6739 =
              let uu____6756 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6759 =
                let uu____6770 =
                  let uu____6779 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6779)  in
                [uu____6770]  in
              (uu____6756, uu____6759)  in
            FStar_Syntax_Syntax.Tm_app uu____6739  in
          mk1 uu____6738  in
        let uu____6815 =
          let uu____6816 = FStar_Syntax_Syntax.mk_binder p  in [uu____6816]
           in
        FStar_Syntax_Util.abs uu____6815 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6841  ->
    match uu___4_6841 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6844 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____7082 =
          match uu____7082 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____7119 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____7122 =
                       let uu____7124 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____7124  in
                     Prims.op_Negation uu____7122)
                   in
                if uu____7119
                then
                  let uu____7126 =
                    let uu____7132 =
                      let uu____7134 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____7136 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____7138 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____7134 uu____7136 uu____7138
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____7132)  in
                  FStar_Errors.raise_err uu____7126
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____7163 = mk_return env t1 s_e  in
                     ((M t1), uu____7163, u_e)))
               | (M t1,N t2) ->
                   let uu____7170 =
                     let uu____7176 =
                       let uu____7178 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____7180 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____7182 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____7178 uu____7180 uu____7182
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____7176)
                      in
                   FStar_Errors.raise_err uu____7170)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_7234 =
            match uu___5_7234 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____7250 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____7271 =
                let uu____7277 =
                  let uu____7279 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____7279
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____7277)  in
              FStar_Errors.raise_error uu____7271 e2.FStar_Syntax_Syntax.pos
          | M uu____7289 ->
              let uu____7290 = check env1 e2 context_nm  in
              strip_m uu____7290
           in
        let uu____7297 =
          let uu____7298 = FStar_Syntax_Subst.compress e  in
          uu____7298.FStar_Syntax_Syntax.n  in
        match uu____7297 with
        | FStar_Syntax_Syntax.Tm_bvar uu____7307 ->
            let uu____7308 = infer env e  in return_if uu____7308
        | FStar_Syntax_Syntax.Tm_name uu____7315 ->
            let uu____7316 = infer env e  in return_if uu____7316
        | FStar_Syntax_Syntax.Tm_fvar uu____7323 ->
            let uu____7324 = infer env e  in return_if uu____7324
        | FStar_Syntax_Syntax.Tm_abs uu____7331 ->
            let uu____7350 = infer env e  in return_if uu____7350
        | FStar_Syntax_Syntax.Tm_constant uu____7357 ->
            let uu____7358 = infer env e  in return_if uu____7358
        | FStar_Syntax_Syntax.Tm_quoted uu____7365 ->
            let uu____7372 = infer env e  in return_if uu____7372
        | FStar_Syntax_Syntax.Tm_app uu____7379 ->
            let uu____7396 = infer env e  in return_if uu____7396
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____7404 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____7404 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____7469) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7475) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7481,uu____7482) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____7523 ->
            let uu____7537 =
              let uu____7539 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7539  in
            failwith uu____7537
        | FStar_Syntax_Syntax.Tm_type uu____7548 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7556 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7578 ->
            let uu____7585 =
              let uu____7587 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7587  in
            failwith uu____7585
        | FStar_Syntax_Syntax.Tm_uvar uu____7596 ->
            let uu____7609 =
              let uu____7611 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7611  in
            failwith uu____7609
        | FStar_Syntax_Syntax.Tm_delayed uu____7620 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7650 =
              let uu____7652 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7652  in
            failwith uu____7650

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
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
          FStar_TypeChecker_Env.EraseUniverses] env.tcenv
         in
      let uu____7682 =
        let uu____7683 = FStar_Syntax_Subst.compress e  in
        uu____7683.FStar_Syntax_Syntax.n  in
      match uu____7682 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7702 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7702
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7753;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7754;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7760 =
                  let uu___807_7761 = rc  in
                  let uu____7762 =
                    let uu____7767 =
                      let uu____7770 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7770  in
                    FStar_Pervasives_Native.Some uu____7767  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___807_7761.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7762;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___807_7761.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7760
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___813_7782 = env  in
            let uu____7783 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7783;
              subst = (uu___813_7782.subst);
              tc_const = (uu___813_7782.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7809  ->
                 match uu____7809 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___820_7832 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___820_7832.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___820_7832.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7833 =
            FStar_List.fold_left
              (fun uu____7864  ->
                 fun uu____7865  ->
                   match (uu____7864, uu____7865) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7923 = is_C c  in
                       if uu____7923
                       then
                         let xw =
                           let uu____7933 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7933
                            in
                         let x =
                           let uu___832_7936 = bv  in
                           let uu____7937 =
                             let uu____7940 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7940  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___832_7936.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___832_7936.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7937
                           }  in
                         let env3 =
                           let uu___835_7942 = env2  in
                           let uu____7943 =
                             let uu____7946 =
                               let uu____7947 =
                                 let uu____7954 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7954)  in
                               FStar_Syntax_Syntax.NT uu____7947  in
                             uu____7946 :: (env2.subst)  in
                           {
                             tcenv = (uu___835_7942.tcenv);
                             subst = uu____7943;
                             tc_const = (uu___835_7942.tc_const)
                           }  in
                         let uu____7959 =
                           let uu____7962 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7963 =
                             let uu____7966 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7966 :: acc  in
                           uu____7962 :: uu____7963  in
                         (env3, uu____7959)
                       else
                         (let x =
                            let uu___838_7972 = bv  in
                            let uu____7973 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___838_7972.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___838_7972.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7973
                            }  in
                          let uu____7976 =
                            let uu____7979 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7979 :: acc  in
                          (env2, uu____7976))) (env1, []) binders1
             in
          (match uu____7833 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7999 =
                 let check_what =
                   let uu____8025 = is_monadic rc_opt1  in
                   if uu____8025 then check_m else check_n  in
                 let uu____8042 = check_what env2 body1  in
                 match uu____8042 with
                 | (t,s_body,u_body) ->
                     let uu____8062 =
                       let uu____8065 =
                         let uu____8066 = is_monadic rc_opt1  in
                         if uu____8066 then M t else N t  in
                       comp_of_nm uu____8065  in
                     (uu____8062, s_body, u_body)
                  in
               (match uu____7999 with
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
                                 let uu____8106 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_8112  ->
                                           match uu___6_8112 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____8115 -> false))
                                    in
                                 if uu____8106
                                 then
                                   let uu____8118 =
                                     FStar_List.filter
                                       (fun uu___7_8122  ->
                                          match uu___7_8122 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____8125 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____8118
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____8136 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_8142  ->
                                         match uu___8_8142 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____8145 -> false))
                                  in
                               if uu____8136
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_8154  ->
                                        match uu___9_8154 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____8157 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____8159 =
                                   let uu____8160 =
                                     let uu____8165 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____8165
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____8160 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____8159
                               else
                                 (let uu____8172 =
                                    let uu___879_8173 = rc  in
                                    let uu____8174 =
                                      let uu____8179 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____8179
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___879_8173.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____8174;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___879_8173.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____8172))
                       in
                    let uu____8184 =
                      let comp1 =
                        let uu____8192 = is_monadic rc_opt1  in
                        let uu____8194 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____8192 uu____8194
                         in
                      let uu____8195 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____8195,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____8184 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____8233 =
                             let uu____8234 =
                               let uu____8253 =
                                 let uu____8256 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____8256 s_rc_opt  in
                               (s_binders1, s_body1, uu____8253)  in
                             FStar_Syntax_Syntax.Tm_abs uu____8234  in
                           mk1 uu____8233  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____8276 =
                             let uu____8277 =
                               let uu____8296 =
                                 let uu____8299 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____8299 u_rc_opt  in
                               (u_binders2, u_body2, uu____8296)  in
                             FStar_Syntax_Syntax.Tm_abs uu____8277  in
                           mk1 uu____8276  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____8315;_};
            FStar_Syntax_Syntax.fv_delta = uu____8316;
            FStar_Syntax_Syntax.fv_qual = uu____8317;_}
          ->
          let uu____8320 =
            let uu____8325 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8325  in
          (match uu____8320 with
           | (uu____8356,t) ->
               let uu____8358 =
                 let uu____8359 = normalize1 t  in N uu____8359  in
               (uu____8358, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8360;
             FStar_Syntax_Syntax.vars = uu____8361;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8440 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8440 with
           | (unary_op1,uu____8464) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8535;
             FStar_Syntax_Syntax.vars = uu____8536;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8632 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8632 with
           | (unary_op1,uu____8656) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8735;
             FStar_Syntax_Syntax.vars = uu____8736;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8774 = infer env a  in
          (match uu____8774 with
           | (t,s,u) ->
               let uu____8790 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8790 with
                | (head1,uu____8814) ->
                    let uu____8839 =
                      let uu____8840 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8840  in
                    let uu____8841 =
                      let uu____8842 =
                        let uu____8843 =
                          let uu____8860 =
                            let uu____8871 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8871]  in
                          (head1, uu____8860)  in
                        FStar_Syntax_Syntax.Tm_app uu____8843  in
                      mk1 uu____8842  in
                    let uu____8908 =
                      let uu____8909 =
                        let uu____8910 =
                          let uu____8927 =
                            let uu____8938 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8938]  in
                          (head1, uu____8927)  in
                        FStar_Syntax_Syntax.Tm_app uu____8910  in
                      mk1 uu____8909  in
                    (uu____8839, uu____8841, uu____8908)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8975;
             FStar_Syntax_Syntax.vars = uu____8976;_},(a1,uu____8978)::a2::[])
          ->
          let uu____9034 = infer env a1  in
          (match uu____9034 with
           | (t,s,u) ->
               let uu____9050 = FStar_Syntax_Util.head_and_args e  in
               (match uu____9050 with
                | (head1,uu____9074) ->
                    let uu____9099 =
                      let uu____9100 =
                        let uu____9101 =
                          let uu____9118 =
                            let uu____9129 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____9129; a2]  in
                          (head1, uu____9118)  in
                        FStar_Syntax_Syntax.Tm_app uu____9101  in
                      mk1 uu____9100  in
                    let uu____9174 =
                      let uu____9175 =
                        let uu____9176 =
                          let uu____9193 =
                            let uu____9204 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____9204; a2]  in
                          (head1, uu____9193)  in
                        FStar_Syntax_Syntax.Tm_app uu____9176  in
                      mk1 uu____9175  in
                    (t, uu____9099, uu____9174)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____9249;
             FStar_Syntax_Syntax.vars = uu____9250;_},uu____9251)
          ->
          let uu____9276 =
            let uu____9282 =
              let uu____9284 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____9284
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____9282)  in
          FStar_Errors.raise_error uu____9276 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____9294;
             FStar_Syntax_Syntax.vars = uu____9295;_},uu____9296)
          ->
          let uu____9321 =
            let uu____9327 =
              let uu____9329 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____9329
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____9327)  in
          FStar_Errors.raise_error uu____9321 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____9365 = check_n env head1  in
          (match uu____9365 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____9388 =
                   let uu____9389 = FStar_Syntax_Subst.compress t  in
                   uu____9389.FStar_Syntax_Syntax.n  in
                 match uu____9388 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____9393 -> true
                 | uu____9409 -> false  in
               let rec flatten1 t =
                 let uu____9431 =
                   let uu____9432 = FStar_Syntax_Subst.compress t  in
                   uu____9432.FStar_Syntax_Syntax.n  in
                 match uu____9431 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____9451);
                                FStar_Syntax_Syntax.pos = uu____9452;
                                FStar_Syntax_Syntax.vars = uu____9453;_})
                     when is_arrow t1 ->
                     let uu____9482 = flatten1 t1  in
                     (match uu____9482 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9582,uu____9583)
                     -> flatten1 e1
                 | uu____9624 ->
                     let uu____9625 =
                       let uu____9631 =
                         let uu____9633 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9633
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9631)  in
                     FStar_Errors.raise_err uu____9625
                  in
               let uu____9651 = flatten1 t_head  in
               (match uu____9651 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9726 =
                          let uu____9732 =
                            let uu____9734 = FStar_Util.string_of_int n1  in
                            let uu____9736 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9738 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9734 uu____9736 uu____9738
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9732)
                           in
                        FStar_Errors.raise_err uu____9726)
                     else ();
                     (let uu____9744 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9744 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9797 args1 =
                            match uu____9797 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9897 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9897
                                 | (binders3,[]) ->
                                     let uu____9935 =
                                       let uu____9936 =
                                         let uu____9939 =
                                           let uu____9940 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9940
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9939
                                          in
                                       uu____9936.FStar_Syntax_Syntax.n  in
                                     (match uu____9935 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9973 =
                                            let uu____9974 =
                                              let uu____9975 =
                                                let uu____9990 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9990)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9975
                                               in
                                            mk1 uu____9974  in
                                          N uu____9973
                                      | uu____10003 -> failwith "wat?")
                                 | ([],uu____10005::uu____10006) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____10059)::binders3,(arg,uu____10062)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____10149 = FStar_List.splitAt n' binders1
                             in
                          (match uu____10149 with
                           | (binders2,uu____10183) ->
                               let uu____10216 =
                                 let uu____10239 =
                                   FStar_List.map2
                                     (fun uu____10301  ->
                                        fun uu____10302  ->
                                          match (uu____10301, uu____10302)
                                          with
                                          | ((bv,uu____10350),(arg,q)) ->
                                              let uu____10379 =
                                                let uu____10380 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____10380.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____10379 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____10401 ->
                                                   let uu____10402 =
                                                     let uu____10409 =
                                                       star_type' env arg  in
                                                     (uu____10409, q)  in
                                                   (uu____10402, [(arg, q)])
                                               | uu____10446 ->
                                                   let uu____10447 =
                                                     check_n env arg  in
                                                   (match uu____10447 with
                                                    | (uu____10472,s_arg,u_arg)
                                                        ->
                                                        let uu____10475 =
                                                          let uu____10484 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____10484
                                                          then
                                                            let uu____10495 =
                                                              let uu____10502
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____10502,
                                                                q)
                                                               in
                                                            [uu____10495;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____10475))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____10239  in
                               (match uu____10216 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10630 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10643 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10630, uu____10643)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10712) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10718) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10724,uu____10725) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10767 =
            let uu____10768 = env.tc_const c  in N uu____10768  in
          (uu____10767, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10775 ->
          let uu____10789 =
            let uu____10791 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10791  in
          failwith uu____10789
      | FStar_Syntax_Syntax.Tm_type uu____10800 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10808 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10830 ->
          let uu____10837 =
            let uu____10839 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10839  in
          failwith uu____10837
      | FStar_Syntax_Syntax.Tm_uvar uu____10848 ->
          let uu____10861 =
            let uu____10863 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10863  in
          failwith uu____10861
      | FStar_Syntax_Syntax.Tm_delayed uu____10872 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10902 =
            let uu____10904 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10904  in
          failwith uu____10902

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____10953 = check_n env e0  in
          match uu____10953 with
          | (uu____10966,s_e0,u_e0) ->
              let uu____10969 =
                let uu____10998 =
                  FStar_List.map
                    (fun b  ->
                       let uu____11059 = FStar_Syntax_Subst.open_branch b  in
                       match uu____11059 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1154_11101 = env  in
                             let uu____11102 =
                               let uu____11103 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____11103
                                in
                             {
                               tcenv = uu____11102;
                               subst = (uu___1154_11101.subst);
                               tc_const = (uu___1154_11101.tc_const)
                             }  in
                           let uu____11106 = f env1 body  in
                           (match uu____11106 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____11178 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10998  in
              (match uu____10969 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____11284 = FStar_List.hd nms  in
                     match uu____11284 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_11293  ->
                          match uu___10_11293 with
                          | M uu____11295 -> true
                          | uu____11297 -> false) nms
                      in
                   let uu____11299 =
                     let uu____11336 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____11426  ->
                              match uu____11426 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11610 =
                                         check env original_body (M t2)  in
                                       (match uu____11610 with
                                        | (uu____11647,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11686,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____11336  in
                   (match uu____11299 with
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
                              (fun uu____11875  ->
                                 match uu____11875 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11926 =
                                         let uu____11927 =
                                           let uu____11944 =
                                             let uu____11955 =
                                               let uu____11964 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11967 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11964, uu____11967)  in
                                             [uu____11955]  in
                                           (s_body, uu____11944)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11927
                                          in
                                       mk1 uu____11926  in
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
                            let uu____12102 =
                              let uu____12103 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12103]  in
                            let uu____12122 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____12102 uu____12122
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____12146 =
                              let uu____12155 =
                                let uu____12162 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____12162
                                 in
                              [uu____12155]  in
                            let uu____12181 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____12146 uu____12181
                             in
                          let uu____12184 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____12223 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____12184, uu____12223)
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
                           let uu____12333 =
                             let uu____12334 =
                               let uu____12335 =
                                 let uu____12362 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____12362,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12335
                                in
                             mk1 uu____12334  in
                           let uu____12421 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____12333, uu____12421))))

and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
                 FStar_Syntax_Syntax.term))
            -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
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
              let uu____12486 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12486]  in
            let uu____12505 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12505 with
            | (x_binders1,e21) ->
                let uu____12518 = infer env e1  in
                (match uu____12518 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12535 = is_C t1  in
                       if uu____12535
                       then
                         let uu___1240_12538 = binding  in
                         let uu____12539 =
                           let uu____12542 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12542  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1240_12538.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1240_12538.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12539;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1240_12538.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1240_12538.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1240_12538.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1240_12538.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1243_12546 = env  in
                       let uu____12547 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1245_12549 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1245_12549.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1245_12549.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12547;
                         subst = (uu___1243_12546.subst);
                         tc_const = (uu___1243_12546.tc_const)
                       }  in
                     let uu____12550 = proceed env1 e21  in
                     (match uu____12550 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1252_12567 = binding  in
                            let uu____12568 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1252_12567.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1252_12567.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12568;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1252_12567.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1252_12567.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1252_12567.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1252_12567.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12571 =
                            let uu____12572 =
                              let uu____12573 =
                                let uu____12587 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1255_12604 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1255_12604.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1255_12604.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1255_12604.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1255_12604.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1255_12604.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1255_12604.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12587)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12573  in
                            mk1 uu____12572  in
                          let uu____12605 =
                            let uu____12606 =
                              let uu____12607 =
                                let uu____12621 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1257_12638 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1257_12638.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1257_12638.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1257_12638.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1257_12638.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1257_12638.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1257_12638.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12621)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12607  in
                            mk1 uu____12606  in
                          (nm_rec, uu____12571, uu____12605))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1264_12643 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1264_12643.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1264_12643.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1264_12643.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1264_12643.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1264_12643.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1267_12645 = env  in
                       let uu____12646 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1269_12648 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1269_12648.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1269_12648.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12646;
                         subst = (uu___1267_12645.subst);
                         tc_const = (uu___1267_12645.tc_const)
                       }  in
                     let uu____12649 = ensure_m env1 e21  in
                     (match uu____12649 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12673 =
                              let uu____12674 =
                                let uu____12691 =
                                  let uu____12702 =
                                    let uu____12711 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12714 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12711, uu____12714)  in
                                  [uu____12702]  in
                                (s_e2, uu____12691)  in
                              FStar_Syntax_Syntax.Tm_app uu____12674  in
                            mk1 uu____12673  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12756 =
                              let uu____12757 =
                                let uu____12774 =
                                  let uu____12785 =
                                    let uu____12794 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12794)  in
                                  [uu____12785]  in
                                (s_e1, uu____12774)  in
                              FStar_Syntax_Syntax.Tm_app uu____12757  in
                            mk1 uu____12756  in
                          let uu____12830 =
                            let uu____12831 =
                              let uu____12832 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12832]  in
                            FStar_Syntax_Util.abs uu____12831 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12851 =
                            let uu____12852 =
                              let uu____12853 =
                                let uu____12867 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1281_12884 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1281_12884.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1281_12884.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1281_12884.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1281_12884.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1281_12884.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1281_12884.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12867)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12853  in
                            mk1 uu____12852  in
                          ((M t2), uu____12830, uu____12851)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12894 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12894  in
      let uu____12895 = check env e mn  in
      match uu____12895 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12911 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12934 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12934  in
      let uu____12935 = check env e mn  in
      match uu____12935 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12951 -> failwith "[check_m]: impossible"

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
        (let uu____12984 =
           let uu____12986 = is_C c  in Prims.op_Negation uu____12986  in
         if uu____12984 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____13000 =
           let uu____13001 = FStar_Syntax_Subst.compress c  in
           uu____13001.FStar_Syntax_Syntax.n  in
         match uu____13000 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____13030 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____13030 with
              | (wp_head,wp_args) ->
                  ((let uu____13074 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____13093 =
                           let uu____13095 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____13095
                            in
                         Prims.op_Negation uu____13093)
                       in
                    if uu____13074 then failwith "mismatch" else ());
                   (let uu____13108 =
                      let uu____13109 =
                        let uu____13126 =
                          FStar_List.map2
                            (fun uu____13164  ->
                               fun uu____13165  ->
                                 match (uu____13164, uu____13165) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____13227 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____13227
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____13236 =
                                         let uu____13238 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____13238 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____13236
                                       then
                                         let uu____13240 =
                                           let uu____13246 =
                                             let uu____13248 =
                                               print_implicit q  in
                                             let uu____13250 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____13248 uu____13250
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____13246)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____13240
                                       else ());
                                      (let uu____13256 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____13256, q)))) args wp_args
                           in
                        (head1, uu____13126)  in
                      FStar_Syntax_Syntax.Tm_app uu____13109  in
                    mk1 uu____13108)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____13302 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____13302 with
              | (binders_orig,comp1) ->
                  let uu____13309 =
                    let uu____13326 =
                      FStar_List.map
                        (fun uu____13366  ->
                           match uu____13366 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____13394 = is_C h  in
                               if uu____13394
                               then
                                 let w' =
                                   let uu____13410 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____13410
                                    in
                                 let uu____13412 =
                                   let uu____13421 =
                                     let uu____13430 =
                                       let uu____13437 =
                                         let uu____13438 =
                                           let uu____13439 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____13439  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____13438
                                          in
                                       (uu____13437, q)  in
                                     [uu____13430]  in
                                   (w', q) :: uu____13421  in
                                 (w', uu____13412)
                               else
                                 (let x =
                                    let uu____13473 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13473
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____13326  in
                  (match uu____13309 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13547 =
                           let uu____13550 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13550
                            in
                         FStar_Syntax_Subst.subst_comp uu____13547 comp1  in
                       let app =
                         let uu____13554 =
                           let uu____13555 =
                             let uu____13572 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13591 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13592 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13591, uu____13592)) bvs
                                in
                             (wp, uu____13572)  in
                           FStar_Syntax_Syntax.Tm_app uu____13555  in
                         mk1 uu____13554  in
                       let comp3 =
                         let uu____13607 = type_of_comp comp2  in
                         let uu____13608 = is_monadic_comp comp2  in
                         trans_G env uu____13607 uu____13608 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13611,uu____13612) ->
             trans_F_ env e wp
         | uu____13653 -> failwith "impossible trans_F_")

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
            let uu____13661 =
              let uu____13662 = star_type' env h  in
              let uu____13665 =
                let uu____13676 =
                  let uu____13685 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13685)  in
                [uu____13676]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13662;
                FStar_Syntax_Syntax.effect_args = uu____13665;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13661
          else
            (let uu____13711 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13711)

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
    fun t  -> let uu____13732 = n env.tcenv t  in star_type' env uu____13732
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13752 = n env.tcenv t  in check_n env uu____13752
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13769 = n env.tcenv c  in
        let uu____13770 = n env.tcenv wp  in
        trans_F_ env uu____13769 uu____13770
  