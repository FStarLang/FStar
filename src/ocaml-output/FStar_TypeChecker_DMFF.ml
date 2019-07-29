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
                    if (FStar_List.length binders) > Prims.int_zero
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
                             (Prims.of_int (2))) FStar_Pervasives_Native.None
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
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1926 =
                        let uu____1935 =
                          let uu____1942 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1942  in
                        [uu____1935]  in
                      let uu____1955 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1926 uu____1955  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1963 =
                        let uu____1974 =
                          let uu____1977 =
                            let uu____1978 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1978  in
                          let uu____1997 =
                            let uu____2000 =
                              let uu____2001 =
                                let uu____2012 =
                                  let uu____2015 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2015]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2012
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2001  in
                            [uu____2000]  in
                          uu____1977 :: uu____1997  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1974
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1963  in
                    let uu____2032 =
                      let uu____2033 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2033  in
                    FStar_Syntax_Util.abs uu____2032 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2049 = mk_lid "wp_close"  in
                    register env1 uu____2049 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2060 =
                      let uu____2061 =
                        let uu____2062 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2062
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2061  in
                    FStar_Pervasives_Native.Some uu____2060  in
                  let mk_forall1 x body =
                    let uu____2074 =
                      let uu____2081 =
                        let uu____2082 =
                          let uu____2099 =
                            let uu____2110 =
                              let uu____2119 =
                                let uu____2120 =
                                  let uu____2121 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2121]  in
                                FStar_Syntax_Util.abs uu____2120 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2119  in
                            [uu____2110]  in
                          (FStar_Syntax_Util.tforall, uu____2099)  in
                        FStar_Syntax_Syntax.Tm_app uu____2082  in
                      FStar_Syntax_Syntax.mk uu____2081  in
                    uu____2074 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2179 =
                      let uu____2180 = FStar_Syntax_Subst.compress t  in
                      uu____2180.FStar_Syntax_Syntax.n  in
                    match uu____2179 with
                    | FStar_Syntax_Syntax.Tm_type uu____2184 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2217  ->
                              match uu____2217 with
                              | (b,uu____2226) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2231 -> true  in
                  let rec is_monotonic t =
                    let uu____2244 =
                      let uu____2245 = FStar_Syntax_Subst.compress t  in
                      uu____2245.FStar_Syntax_Syntax.n  in
                    match uu____2244 with
                    | FStar_Syntax_Syntax.Tm_type uu____2249 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2282  ->
                              match uu____2282 with
                              | (b,uu____2291) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2296 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2370 =
                      let uu____2371 = FStar_Syntax_Subst.compress t1  in
                      uu____2371.FStar_Syntax_Syntax.n  in
                    match uu____2370 with
                    | FStar_Syntax_Syntax.Tm_type uu____2376 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2379);
                                      FStar_Syntax_Syntax.pos = uu____2380;
                                      FStar_Syntax_Syntax.vars = uu____2381;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2425 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2425
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2435 =
                              let uu____2438 =
                                let uu____2449 =
                                  let uu____2458 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2458  in
                                [uu____2449]  in
                              FStar_Syntax_Util.mk_app x uu____2438  in
                            let uu____2475 =
                              let uu____2478 =
                                let uu____2489 =
                                  let uu____2498 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2498  in
                                [uu____2489]  in
                              FStar_Syntax_Util.mk_app y uu____2478  in
                            mk_rel1 b uu____2435 uu____2475  in
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
                             let uu____2522 =
                               let uu____2525 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2528 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2525 uu____2528  in
                             let uu____2531 =
                               let uu____2534 =
                                 let uu____2537 =
                                   let uu____2548 =
                                     let uu____2557 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2557
                                      in
                                   [uu____2548]  in
                                 FStar_Syntax_Util.mk_app x uu____2537  in
                               let uu____2574 =
                                 let uu____2577 =
                                   let uu____2588 =
                                     let uu____2597 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2597
                                      in
                                   [uu____2588]  in
                                 FStar_Syntax_Util.mk_app y uu____2577  in
                               mk_rel1 b uu____2534 uu____2574  in
                             FStar_Syntax_Util.mk_imp uu____2522 uu____2531
                              in
                           let uu____2614 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2614)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2617);
                                      FStar_Syntax_Syntax.pos = uu____2618;
                                      FStar_Syntax_Syntax.vars = uu____2619;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2663 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2663
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2673 =
                              let uu____2676 =
                                let uu____2687 =
                                  let uu____2696 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2696  in
                                [uu____2687]  in
                              FStar_Syntax_Util.mk_app x uu____2676  in
                            let uu____2713 =
                              let uu____2716 =
                                let uu____2727 =
                                  let uu____2736 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2736  in
                                [uu____2727]  in
                              FStar_Syntax_Util.mk_app y uu____2716  in
                            mk_rel1 b uu____2673 uu____2713  in
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
                             let uu____2760 =
                               let uu____2763 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2766 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2763 uu____2766  in
                             let uu____2769 =
                               let uu____2772 =
                                 let uu____2775 =
                                   let uu____2786 =
                                     let uu____2795 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2795
                                      in
                                   [uu____2786]  in
                                 FStar_Syntax_Util.mk_app x uu____2775  in
                               let uu____2812 =
                                 let uu____2815 =
                                   let uu____2826 =
                                     let uu____2835 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2835
                                      in
                                   [uu____2826]  in
                                 FStar_Syntax_Util.mk_app y uu____2815  in
                               mk_rel1 b uu____2772 uu____2812  in
                             FStar_Syntax_Util.mk_imp uu____2760 uu____2769
                              in
                           let uu____2852 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2852)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___231_2891 = t1  in
                          let uu____2892 =
                            let uu____2893 =
                              let uu____2908 =
                                let uu____2911 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2911  in
                              ([binder], uu____2908)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2893  in
                          {
                            FStar_Syntax_Syntax.n = uu____2892;
                            FStar_Syntax_Syntax.pos =
                              (uu___231_2891.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___231_2891.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2934 ->
                        failwith "unhandled arrow"
                    | uu____2952 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____2989 =
                        let uu____2990 = FStar_Syntax_Subst.compress t1  in
                        uu____2990.FStar_Syntax_Syntax.n  in
                      match uu____2989 with
                      | FStar_Syntax_Syntax.Tm_type uu____2993 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3020 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3020
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3041 =
                                let uu____3042 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3042 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3041
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   Prims.int_one)
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3072 =
                            let uu____3083 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3101  ->
                                     match uu____3101 with
                                     | (t2,q) ->
                                         let uu____3121 = project i x  in
                                         let uu____3124 = project i y  in
                                         mk_stronger t2 uu____3121 uu____3124)
                                args
                               in
                            match uu____3083 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3072 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3178);
                                      FStar_Syntax_Syntax.pos = uu____3179;
                                      FStar_Syntax_Syntax.vars = uu____3180;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3224  ->
                                   match uu____3224 with
                                   | (bv,q) ->
                                       let uu____3238 =
                                         let uu____3240 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3240  in
                                       FStar_Syntax_Syntax.gen_bv uu____3238
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3249 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3249) bvs
                             in
                          let body =
                            let uu____3251 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3254 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3251 uu____3254  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3263);
                                      FStar_Syntax_Syntax.pos = uu____3264;
                                      FStar_Syntax_Syntax.vars = uu____3265;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3309  ->
                                   match uu____3309 with
                                   | (bv,q) ->
                                       let uu____3323 =
                                         let uu____3325 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3325  in
                                       FStar_Syntax_Syntax.gen_bv uu____3323
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3334 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3334) bvs
                             in
                          let body =
                            let uu____3336 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3339 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3336 uu____3339  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3346 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3349 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3352 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3355 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3349 uu____3352 uu____3355  in
                    let uu____3358 =
                      let uu____3359 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3359  in
                    FStar_Syntax_Util.abs uu____3358 body ret_tot_type  in
                  let stronger1 =
                    let uu____3401 = mk_lid "stronger"  in
                    register env1 uu____3401 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let mrelation_from_interp interp =
                    let repr_a =
                      let uu____3415 =
                        let uu____3426 =
                          let uu____3435 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          FStar_Syntax_Syntax.as_arg uu____3435  in
                        [uu____3426]  in
                      FStar_Syntax_Util.mk_app
                        (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                        uu____3415
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
                      let uu____3459 =
                        let uu____3470 =
                          let uu____3479 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          FStar_Syntax_Syntax.as_arg uu____3479  in
                        let uu____3480 =
                          let uu____3491 =
                            let uu____3500 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            FStar_Syntax_Syntax.as_arg uu____3500  in
                          let uu____3501 =
                            let uu____3512 =
                              let uu____3521 =
                                let uu____3522 =
                                  let uu____3533 =
                                    let uu____3542 =
                                      FStar_Syntax_Syntax.bv_to_name a1  in
                                    FStar_Syntax_Syntax.iarg uu____3542  in
                                  let uu____3543 =
                                    let uu____3554 =
                                      let uu____3563 =
                                        FStar_Syntax_Syntax.bv_to_name c  in
                                      FStar_Syntax_Syntax.as_arg uu____3563
                                       in
                                    [uu____3554]  in
                                  uu____3533 :: uu____3543  in
                                FStar_Syntax_Util.mk_app interp uu____3522
                                 in
                              FStar_Syntax_Syntax.as_arg uu____3521  in
                            [uu____3512]  in
                          uu____3491 :: uu____3501  in
                        uu____3470 :: uu____3480  in
                      FStar_Syntax_Util.mk_app stronger2 uu____3459  in
                    let abs1 =
                      let uu____3623 =
                        let uu____3624 =
                          let uu____3633 =
                            FStar_Syntax_Syntax.mk_implicit_binder a1  in
                          let uu____3640 =
                            let uu____3649 = FStar_Syntax_Syntax.mk_binder c
                               in
                            let uu____3656 =
                              let uu____3665 =
                                FStar_Syntax_Syntax.mk_binder wp  in
                              [uu____3665]  in
                            uu____3649 :: uu____3656  in
                          uu____3633 :: uu____3640  in
                        FStar_List.append binders uu____3624  in
                      FStar_Syntax_Util.abs uu____3623 body ret_tot_type  in
                    abs1  in
                  let mrelation =
                    match ((ed.FStar_Syntax_Syntax.interp),
                            (ed.FStar_Syntax_Syntax.mrelation))
                    with
                    | (uu____3711,FStar_Pervasives_Native.Some t) ->
                        FStar_Pervasives_Native.Some
                          (FStar_Pervasives_Native.snd t)
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        FStar_Pervasives_Native.None
                    | (FStar_Pervasives_Native.Some
                       i,FStar_Pervasives_Native.None ) ->
                        let uu____3732 =
                          mrelation_from_interp
                            (FStar_Pervasives_Native.snd i)
                           in
                        FStar_Pervasives_Native.Some uu____3732
                     in
                  let mrelation1 =
                    let uu____3742 =
                      let uu____3749 = mk_lid "mrelation"  in
                      register env1 uu____3749  in
                    FStar_Util.map_opt mrelation uu____3742  in
                  let mrelation2 =
                    FStar_Util.map_opt mrelation1 mk_generic_app  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3761 = FStar_Util.prefix gamma  in
                    match uu____3761 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3827 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3827
                             in
                          let uu____3832 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3832 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3842 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3842  in
                              let guard_free1 =
                                let uu____3854 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3854  in
                              let pat =
                                let uu____3858 =
                                  let uu____3869 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3869]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3858
                                 in
                              let pattern_guarded_body =
                                let uu____3897 =
                                  let uu____3898 =
                                    let uu____3905 =
                                      let uu____3906 =
                                        let uu____3927 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1
                                           in
                                        let uu____3932 =
                                          let uu____3945 =
                                            let uu____3956 =
                                              FStar_Syntax_Syntax.as_arg pat
                                               in
                                            [uu____3956]  in
                                          [uu____3945]  in
                                        (uu____3927, uu____3932)  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3906
                                       in
                                    (body, uu____3905)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3898  in
                                mk1 uu____3897  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____4019 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____4028 =
                            let uu____4031 =
                              let uu____4032 =
                                let uu____4035 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____4038 =
                                  let uu____4049 = args_of_binders1 wp_args
                                     in
                                  let uu____4052 =
                                    let uu____4055 =
                                      let uu____4056 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____4056
                                       in
                                    [uu____4055]  in
                                  FStar_List.append uu____4049 uu____4052  in
                                FStar_Syntax_Util.mk_app uu____4035
                                  uu____4038
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____4032  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____4031
                             in
                          FStar_Syntax_Util.abs gamma uu____4028
                            ret_gtot_type
                           in
                        let uu____4057 =
                          let uu____4058 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____4058  in
                        FStar_Syntax_Util.abs uu____4057 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____4074 = mk_lid "ite_wp"  in
                    register env1 uu____4074 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____4082 = FStar_Util.prefix gamma  in
                    match uu____4082 with
                    | (wp_args,post) ->
                        let uu____4137 =
                          FStar_Syntax_Util.arrow_formals_comp
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        (match uu____4137 with
                         | (bs,uu____4153) ->
                             let bs1 =
                               FStar_List.map
                                 FStar_Syntax_Syntax.freshen_binder bs
                                in
                             let args =
                               FStar_List.map
                                 (fun uu____4216  ->
                                    match uu____4216 with
                                    | (bv,q) ->
                                        let uu____4235 =
                                          FStar_Syntax_Syntax.bv_to_name bv
                                           in
                                        (uu____4235, q)) bs1
                                in
                             let body =
                               let uu____4239 =
                                 let uu____4240 =
                                   FStar_All.pipe_left
                                     FStar_Syntax_Syntax.bv_to_name
                                     (FStar_Pervasives_Native.fst post)
                                    in
                                 FStar_Syntax_Util.mk_app uu____4240 args  in
                               FStar_Syntax_Util.close_forall_no_univs bs1
                                 uu____4239
                                in
                             let uu____4247 =
                               let uu____4248 =
                                 let uu____4257 =
                                   FStar_Syntax_Syntax.binders_of_list [a1]
                                    in
                                 FStar_List.append uu____4257 gamma  in
                               FStar_List.append binders uu____4248  in
                             FStar_Syntax_Util.abs uu____4247 body
                               ret_gtot_type)
                     in
                  let null_wp1 =
                    let uu____4279 = mk_lid "null_wp"  in
                    register env1 uu____4279 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____4292 =
                        let uu____4303 =
                          let uu____4306 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4307 =
                            let uu____4310 =
                              let uu____4311 =
                                let uu____4322 =
                                  let uu____4331 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4331  in
                                [uu____4322]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4311
                               in
                            let uu____4348 =
                              let uu____4351 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4351]  in
                            uu____4310 :: uu____4348  in
                          uu____4306 :: uu____4307  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4303
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____4292  in
                    let uu____4360 =
                      let uu____4361 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4361  in
                    FStar_Syntax_Util.abs uu____4360 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4377 = mk_lid "wp_trivial"  in
                    register env1 uu____4377 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4383 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4383
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4395 =
                      let uu____4396 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4396  in
                    let uu____4422 =
                      let uu___366_4423 = ed  in
                      let uu____4424 =
                        let uu____4425 = c wp_if_then_else2  in
                        ([], uu____4425)  in
                      let uu____4432 =
                        let uu____4433 = c ite_wp2  in ([], uu____4433)  in
                      let uu____4440 =
                        let uu____4441 = c stronger2  in ([], uu____4441)  in
                      let uu____4448 =
                        let uu____4449 = c wp_close2  in ([], uu____4449)  in
                      let uu____4456 =
                        let uu____4457 = c wp_trivial2  in ([], uu____4457)
                         in
                      let uu____4464 =
                        FStar_Util.map_opt mrelation2
                          (fun t  ->
                             let uu____4476 = c t  in ([], uu____4476))
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___366_4423.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___366_4423.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___366_4423.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___366_4423.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.spec =
                          (uu___366_4423.FStar_Syntax_Syntax.spec);
                        FStar_Syntax_Syntax.signature =
                          (uu___366_4423.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.if_then_else = uu____4424;
                        FStar_Syntax_Syntax.ite_wp = uu____4432;
                        FStar_Syntax_Syntax.stronger = uu____4440;
                        FStar_Syntax_Syntax.close_wp = uu____4448;
                        FStar_Syntax_Syntax.trivial = uu____4456;
                        FStar_Syntax_Syntax.repr =
                          (uu___366_4423.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.elaborated =
                          (uu___366_4423.FStar_Syntax_Syntax.elaborated);
                        FStar_Syntax_Syntax.spec_dm4f =
                          (uu___366_4423.FStar_Syntax_Syntax.spec_dm4f);
                        FStar_Syntax_Syntax.interp =
                          (uu___366_4423.FStar_Syntax_Syntax.interp);
                        FStar_Syntax_Syntax.mrelation = uu____4464;
                        FStar_Syntax_Syntax.actions =
                          (uu___366_4423.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___366_4423.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4395, uu____4422)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___372_4496 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___372_4496.subst);
        tc_const = (uu___372_4496.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4517 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4536 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4556) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4570  ->
                match uu___0_4570 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4573 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4575 ->
        let uu____4576 =
          let uu____4582 =
            let uu____4584 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4584
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4582)  in
        FStar_Errors.raise_error uu____4576 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4594  ->
    match uu___1_4594 with
    | N t ->
        let uu____4597 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4597
    | M t ->
        let uu____4601 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4601
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4610,c) -> nm_of_comp c
    | uu____4632 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4645 = nm_of_comp c  in
    match uu____4645 with | M uu____4647 -> true | N uu____4649 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4660 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4676 =
        let uu____4685 =
          let uu____4692 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4692  in
        [uu____4685]  in
      let uu____4711 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4676 uu____4711  in
    let uu____4714 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4714
  
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
        let uu____4756 =
          let uu____4757 =
            let uu____4772 =
              let uu____4781 =
                let uu____4788 =
                  let uu____4789 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4789  in
                let uu____4790 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4788, uu____4790)  in
              [uu____4781]  in
            let uu____4808 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4772, uu____4808)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4757  in
        mk1 uu____4756

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4848) ->
          let binders1 =
            FStar_List.map
              (fun uu____4894  ->
                 match uu____4894 with
                 | (bv,aqual) ->
                     let uu____4913 =
                       let uu___422_4914 = bv  in
                       let uu____4915 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___422_4914.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___422_4914.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4915
                       }  in
                     (uu____4913, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4920,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4922);
                             FStar_Syntax_Syntax.pos = uu____4923;
                             FStar_Syntax_Syntax.vars = uu____4924;_})
               ->
               let uu____4953 =
                 let uu____4954 =
                   let uu____4969 =
                     let uu____4972 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4972  in
                   (binders1, uu____4969)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4954  in
               mk1 uu____4953
           | uu____4983 ->
               let uu____4984 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4984 with
                | N hn ->
                    let uu____4986 =
                      let uu____4987 =
                        let uu____5002 =
                          let uu____5005 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____5005  in
                        (binders1, uu____5002)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4987  in
                    mk1 uu____4986
                | M a ->
                    let uu____5017 =
                      let uu____5018 =
                        let uu____5033 =
                          let uu____5042 =
                            let uu____5051 =
                              let uu____5058 =
                                let uu____5059 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____5059  in
                              let uu____5060 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____5058, uu____5060)  in
                            [uu____5051]  in
                          FStar_List.append binders1 uu____5042  in
                        let uu____5084 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____5033, uu____5084)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____5018  in
                    mk1 uu____5017))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____5178 = f x  in
                    FStar_Util.string_builder_append strb uu____5178);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____5187 = f x1  in
                         FStar_Util.string_builder_append strb uu____5187))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____5191 =
              let uu____5197 =
                let uu____5199 = FStar_Syntax_Print.term_to_string t2  in
                let uu____5201 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____5199 uu____5201
                 in
              (FStar_Errors.Warning_DependencyFound, uu____5197)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____5191  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____5223 =
              let uu____5224 = FStar_Syntax_Subst.compress ty  in
              uu____5224.FStar_Syntax_Syntax.n  in
            match uu____5223 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5250 =
                  let uu____5252 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____5252  in
                if uu____5250
                then false
                else
                  (try
                     (fun uu___471_5269  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____5293 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____5293 s  in
                              let uu____5296 =
                                let uu____5298 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____5298  in
                              if uu____5296
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____5304 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____5304 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5329  ->
                                          match uu____5329 with
                                          | (bv,uu____5341) ->
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
                                   if k > Prims.int_zero
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found  -> false)
            | uu____5369 ->
                ((let uu____5371 =
                    let uu____5377 =
                      let uu____5379 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5379
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5377)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5371);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5395 =
              let uu____5396 = FStar_Syntax_Subst.compress head2  in
              uu____5396.FStar_Syntax_Syntax.n  in
            match uu____5395 with
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
                  (let uu____5402 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5402)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5405 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5405 with
                 | ((uu____5415,ty),uu____5417) ->
                     let uu____5422 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5422
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5435 =
                         let uu____5436 = FStar_Syntax_Subst.compress res  in
                         uu____5436.FStar_Syntax_Syntax.n  in
                       (match uu____5435 with
                        | FStar_Syntax_Syntax.Tm_app uu____5440 -> true
                        | uu____5458 ->
                            ((let uu____5460 =
                                let uu____5466 =
                                  let uu____5468 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5468
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5466)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5460);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5476 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5478 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5481) ->
                is_valid_application t2
            | uu____5486 -> false  in
          let uu____5488 = is_valid_application head1  in
          if uu____5488
          then
            let uu____5491 =
              let uu____5492 =
                let uu____5509 =
                  FStar_List.map
                    (fun uu____5538  ->
                       match uu____5538 with
                       | (t2,qual) ->
                           let uu____5563 = star_type' env t2  in
                           (uu____5563, qual)) args
                   in
                (head1, uu____5509)  in
              FStar_Syntax_Syntax.Tm_app uu____5492  in
            mk1 uu____5491
          else
            (let uu____5580 =
               let uu____5586 =
                 let uu____5588 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5588
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5586)  in
             FStar_Errors.raise_err uu____5580)
      | FStar_Syntax_Syntax.Tm_bvar uu____5592 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5593 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5594 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5595 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5623 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5623 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___543_5631 = env  in
                 let uu____5632 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5632;
                   subst = (uu___543_5631.subst);
                   tc_const = (uu___543_5631.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 = [FStar_Syntax_Syntax.DB (Prims.int_zero, x1)]  in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, Prims.int_zero)]  in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___558_5659 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___558_5659.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___558_5659.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5666 =
            let uu____5667 =
              let uu____5674 = star_type' env t2  in (uu____5674, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5667  in
          mk1 uu____5666
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5726 =
            let uu____5727 =
              let uu____5754 = star_type' env e  in
              let uu____5757 =
                let uu____5774 =
                  let uu____5783 = star_type' env t2  in
                  FStar_Util.Inl uu____5783  in
                (uu____5774, FStar_Pervasives_Native.None)  in
              (uu____5754, uu____5757, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5727  in
          mk1 uu____5726
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5871 =
            let uu____5872 =
              let uu____5899 = star_type' env e  in
              let uu____5902 =
                let uu____5919 =
                  let uu____5928 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5928  in
                (uu____5919, FStar_Pervasives_Native.None)  in
              (uu____5899, uu____5902, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5872  in
          mk1 uu____5871
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5969,(uu____5970,FStar_Pervasives_Native.Some uu____5971),uu____5972)
          ->
          let uu____6021 =
            let uu____6027 =
              let uu____6029 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____6029
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6027)  in
          FStar_Errors.raise_err uu____6021
      | FStar_Syntax_Syntax.Tm_refine uu____6033 ->
          let uu____6040 =
            let uu____6046 =
              let uu____6048 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____6048
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6046)  in
          FStar_Errors.raise_err uu____6040
      | FStar_Syntax_Syntax.Tm_uinst uu____6052 ->
          let uu____6059 =
            let uu____6065 =
              let uu____6067 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____6067
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6065)  in
          FStar_Errors.raise_err uu____6059
      | FStar_Syntax_Syntax.Tm_quoted uu____6071 ->
          let uu____6078 =
            let uu____6084 =
              let uu____6086 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____6086
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6084)  in
          FStar_Errors.raise_err uu____6078
      | FStar_Syntax_Syntax.Tm_constant uu____6090 ->
          let uu____6091 =
            let uu____6097 =
              let uu____6099 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____6099
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6097)  in
          FStar_Errors.raise_err uu____6091
      | FStar_Syntax_Syntax.Tm_match uu____6103 ->
          let uu____6126 =
            let uu____6132 =
              let uu____6134 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____6134
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6132)  in
          FStar_Errors.raise_err uu____6126
      | FStar_Syntax_Syntax.Tm_let uu____6138 ->
          let uu____6152 =
            let uu____6158 =
              let uu____6160 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____6160
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6158)  in
          FStar_Errors.raise_err uu____6152
      | FStar_Syntax_Syntax.Tm_uvar uu____6164 ->
          let uu____6177 =
            let uu____6183 =
              let uu____6185 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____6185
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6183)  in
          FStar_Errors.raise_err uu____6177
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6189 =
            let uu____6195 =
              let uu____6197 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____6197
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6195)  in
          FStar_Errors.raise_err uu____6189
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6202 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____6202
      | FStar_Syntax_Syntax.Tm_delayed uu____6205 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_6237  ->
    match uu___3_6237 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_6248  ->
                match uu___2_6248 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____6251 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____6261 =
      let uu____6262 = FStar_Syntax_Subst.compress t  in
      uu____6262.FStar_Syntax_Syntax.n  in
    match uu____6261 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____6294 =
            let uu____6295 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____6295  in
          is_C uu____6294  in
        if r
        then
          ((let uu____6319 =
              let uu____6321 =
                FStar_List.for_all
                  (fun uu____6332  ->
                     match uu____6332 with | (h,uu____6341) -> is_C h) args
                 in
              Prims.op_Negation uu____6321  in
            if uu____6319 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6354 =
              let uu____6356 =
                FStar_List.for_all
                  (fun uu____6368  ->
                     match uu____6368 with
                     | (h,uu____6377) ->
                         let uu____6382 = is_C h  in
                         Prims.op_Negation uu____6382) args
                 in
              Prims.op_Negation uu____6356  in
            if uu____6354 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6411 = nm_of_comp comp  in
        (match uu____6411 with
         | M t1 ->
             ((let uu____6415 = is_C t1  in
               if uu____6415 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6424) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6430) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6436,uu____6437) -> is_C t1
    | uu____6478 -> false
  
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
          let uu____6514 =
            let uu____6515 =
              let uu____6532 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6535 =
                let uu____6546 =
                  let uu____6555 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6555)  in
                [uu____6546]  in
              (uu____6532, uu____6535)  in
            FStar_Syntax_Syntax.Tm_app uu____6515  in
          mk1 uu____6514  in
        let uu____6591 =
          let uu____6592 = FStar_Syntax_Syntax.mk_binder p  in [uu____6592]
           in
        FStar_Syntax_Util.abs uu____6591 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6617  ->
    match uu___4_6617 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6620 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6858 =
          match uu____6858 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6895 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6898 =
                       let uu____6900 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6900  in
                     Prims.op_Negation uu____6898)
                   in
                if uu____6895
                then
                  let uu____6902 =
                    let uu____6908 =
                      let uu____6910 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6912 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6914 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6910 uu____6912 uu____6914
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6908)  in
                  FStar_Errors.raise_err uu____6902
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6939 = mk_return env t1 s_e  in
                     ((M t1), uu____6939, u_e)))
               | (M t1,N t2) ->
                   let uu____6946 =
                     let uu____6952 =
                       let uu____6954 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6956 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6958 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6954 uu____6956 uu____6958
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6952)
                      in
                   FStar_Errors.raise_err uu____6946)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_7010 =
            match uu___5_7010 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____7026 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____7047 =
                let uu____7053 =
                  let uu____7055 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____7055
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____7053)  in
              FStar_Errors.raise_error uu____7047 e2.FStar_Syntax_Syntax.pos
          | M uu____7065 ->
              let uu____7066 = check env1 e2 context_nm  in
              strip_m uu____7066
           in
        let uu____7073 =
          let uu____7074 = FStar_Syntax_Subst.compress e  in
          uu____7074.FStar_Syntax_Syntax.n  in
        match uu____7073 with
        | FStar_Syntax_Syntax.Tm_bvar uu____7083 ->
            let uu____7084 = infer env e  in return_if uu____7084
        | FStar_Syntax_Syntax.Tm_name uu____7091 ->
            let uu____7092 = infer env e  in return_if uu____7092
        | FStar_Syntax_Syntax.Tm_fvar uu____7099 ->
            let uu____7100 = infer env e  in return_if uu____7100
        | FStar_Syntax_Syntax.Tm_abs uu____7107 ->
            let uu____7126 = infer env e  in return_if uu____7126
        | FStar_Syntax_Syntax.Tm_constant uu____7133 ->
            let uu____7134 = infer env e  in return_if uu____7134
        | FStar_Syntax_Syntax.Tm_quoted uu____7141 ->
            let uu____7148 = infer env e  in return_if uu____7148
        | FStar_Syntax_Syntax.Tm_app uu____7155 ->
            let uu____7172 = infer env e  in return_if uu____7172
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____7180 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____7180 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____7245) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7251) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7257,uu____7258) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____7299 ->
            let uu____7313 =
              let uu____7315 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7315  in
            failwith uu____7313
        | FStar_Syntax_Syntax.Tm_type uu____7324 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7332 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7354 ->
            let uu____7361 =
              let uu____7363 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7363  in
            failwith uu____7361
        | FStar_Syntax_Syntax.Tm_uvar uu____7372 ->
            let uu____7385 =
              let uu____7387 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7387  in
            failwith uu____7385
        | FStar_Syntax_Syntax.Tm_delayed uu____7396 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7426 =
              let uu____7428 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7428  in
            failwith uu____7426

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
      let uu____7458 =
        let uu____7459 = FStar_Syntax_Subst.compress e  in
        uu____7459.FStar_Syntax_Syntax.n  in
      match uu____7458 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7478 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7478
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7529;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7530;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7536 =
                  let uu___793_7537 = rc  in
                  let uu____7538 =
                    let uu____7543 =
                      let uu____7546 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7546  in
                    FStar_Pervasives_Native.Some uu____7543  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___793_7537.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7538;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___793_7537.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7536
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___799_7558 = env  in
            let uu____7559 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7559;
              subst = (uu___799_7558.subst);
              tc_const = (uu___799_7558.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7585  ->
                 match uu____7585 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___806_7608 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___806_7608.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___806_7608.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7609 =
            FStar_List.fold_left
              (fun uu____7640  ->
                 fun uu____7641  ->
                   match (uu____7640, uu____7641) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7699 = is_C c  in
                       if uu____7699
                       then
                         let xw =
                           let uu____7709 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7709
                            in
                         let x =
                           let uu___818_7712 = bv  in
                           let uu____7713 =
                             let uu____7716 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7716  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___818_7712.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___818_7712.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7713
                           }  in
                         let env3 =
                           let uu___821_7718 = env2  in
                           let uu____7719 =
                             let uu____7722 =
                               let uu____7723 =
                                 let uu____7730 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7730)  in
                               FStar_Syntax_Syntax.NT uu____7723  in
                             uu____7722 :: (env2.subst)  in
                           {
                             tcenv = (uu___821_7718.tcenv);
                             subst = uu____7719;
                             tc_const = (uu___821_7718.tc_const)
                           }  in
                         let uu____7735 =
                           let uu____7738 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7739 =
                             let uu____7742 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7742 :: acc  in
                           uu____7738 :: uu____7739  in
                         (env3, uu____7735)
                       else
                         (let x =
                            let uu___824_7748 = bv  in
                            let uu____7749 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___824_7748.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___824_7748.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7749
                            }  in
                          let uu____7752 =
                            let uu____7755 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7755 :: acc  in
                          (env2, uu____7752))) (env1, []) binders1
             in
          (match uu____7609 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7775 =
                 let check_what =
                   let uu____7801 = is_monadic rc_opt1  in
                   if uu____7801 then check_m else check_n  in
                 let uu____7818 = check_what env2 body1  in
                 match uu____7818 with
                 | (t,s_body,u_body) ->
                     let uu____7838 =
                       let uu____7841 =
                         let uu____7842 = is_monadic rc_opt1  in
                         if uu____7842 then M t else N t  in
                       comp_of_nm uu____7841  in
                     (uu____7838, s_body, u_body)
                  in
               (match uu____7775 with
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
                                 let uu____7882 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7888  ->
                                           match uu___6_7888 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7891 -> false))
                                    in
                                 if uu____7882
                                 then
                                   let uu____7894 =
                                     FStar_List.filter
                                       (fun uu___7_7898  ->
                                          match uu___7_7898 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7901 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7894
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7912 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7918  ->
                                         match uu___8_7918 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7921 -> false))
                                  in
                               if uu____7912
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7930  ->
                                        match uu___9_7930 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7933 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7935 =
                                   let uu____7936 =
                                     let uu____7941 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7941
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7936 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7935
                               else
                                 (let uu____7948 =
                                    let uu___865_7949 = rc  in
                                    let uu____7950 =
                                      let uu____7955 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7955
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___865_7949.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7950;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___865_7949.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7948))
                       in
                    let uu____7960 =
                      let comp1 =
                        let uu____7968 = is_monadic rc_opt1  in
                        let uu____7970 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7968 uu____7970
                         in
                      let uu____7971 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7971,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7960 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____8009 =
                             let uu____8010 =
                               let uu____8029 =
                                 let uu____8032 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____8032 s_rc_opt  in
                               (s_binders1, s_body1, uu____8029)  in
                             FStar_Syntax_Syntax.Tm_abs uu____8010  in
                           mk1 uu____8009  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____8052 =
                             let uu____8053 =
                               let uu____8072 =
                                 let uu____8075 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____8075 u_rc_opt  in
                               (u_binders2, u_body2, uu____8072)  in
                             FStar_Syntax_Syntax.Tm_abs uu____8053  in
                           mk1 uu____8052  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____8091;_};
            FStar_Syntax_Syntax.fv_delta = uu____8092;
            FStar_Syntax_Syntax.fv_qual = uu____8093;_}
          ->
          let uu____8096 =
            let uu____8101 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8101  in
          (match uu____8096 with
           | (uu____8132,t) ->
               let uu____8134 =
                 let uu____8135 = normalize1 t  in N uu____8135  in
               (uu____8134, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8136;
             FStar_Syntax_Syntax.vars = uu____8137;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8216 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8216 with
           | (unary_op1,uu____8240) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8311;
             FStar_Syntax_Syntax.vars = uu____8312;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8408 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8408 with
           | (unary_op1,uu____8432) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8511;
             FStar_Syntax_Syntax.vars = uu____8512;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8550 = infer env a  in
          (match uu____8550 with
           | (t,s,u) ->
               let uu____8566 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8566 with
                | (head1,uu____8590) ->
                    let uu____8615 =
                      let uu____8616 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8616  in
                    let uu____8617 =
                      let uu____8618 =
                        let uu____8619 =
                          let uu____8636 =
                            let uu____8647 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8647]  in
                          (head1, uu____8636)  in
                        FStar_Syntax_Syntax.Tm_app uu____8619  in
                      mk1 uu____8618  in
                    let uu____8684 =
                      let uu____8685 =
                        let uu____8686 =
                          let uu____8703 =
                            let uu____8714 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8714]  in
                          (head1, uu____8703)  in
                        FStar_Syntax_Syntax.Tm_app uu____8686  in
                      mk1 uu____8685  in
                    (uu____8615, uu____8617, uu____8684)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8751;
             FStar_Syntax_Syntax.vars = uu____8752;_},(a1,uu____8754)::a2::[])
          ->
          let uu____8810 = infer env a1  in
          (match uu____8810 with
           | (t,s,u) ->
               let uu____8826 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8826 with
                | (head1,uu____8850) ->
                    let uu____8875 =
                      let uu____8876 =
                        let uu____8877 =
                          let uu____8894 =
                            let uu____8905 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8905; a2]  in
                          (head1, uu____8894)  in
                        FStar_Syntax_Syntax.Tm_app uu____8877  in
                      mk1 uu____8876  in
                    let uu____8950 =
                      let uu____8951 =
                        let uu____8952 =
                          let uu____8969 =
                            let uu____8980 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8980; a2]  in
                          (head1, uu____8969)  in
                        FStar_Syntax_Syntax.Tm_app uu____8952  in
                      mk1 uu____8951  in
                    (t, uu____8875, uu____8950)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____9025;
             FStar_Syntax_Syntax.vars = uu____9026;_},uu____9027)
          ->
          let uu____9052 =
            let uu____9058 =
              let uu____9060 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____9060
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____9058)  in
          FStar_Errors.raise_error uu____9052 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____9070;
             FStar_Syntax_Syntax.vars = uu____9071;_},uu____9072)
          ->
          let uu____9097 =
            let uu____9103 =
              let uu____9105 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____9105
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____9103)  in
          FStar_Errors.raise_error uu____9097 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____9141 = check_n env head1  in
          (match uu____9141 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____9164 =
                   let uu____9165 = FStar_Syntax_Subst.compress t  in
                   uu____9165.FStar_Syntax_Syntax.n  in
                 match uu____9164 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____9169 -> true
                 | uu____9185 -> false  in
               let rec flatten1 t =
                 let uu____9207 =
                   let uu____9208 = FStar_Syntax_Subst.compress t  in
                   uu____9208.FStar_Syntax_Syntax.n  in
                 match uu____9207 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____9227);
                                FStar_Syntax_Syntax.pos = uu____9228;
                                FStar_Syntax_Syntax.vars = uu____9229;_})
                     when is_arrow t1 ->
                     let uu____9258 = flatten1 t1  in
                     (match uu____9258 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9358,uu____9359)
                     -> flatten1 e1
                 | uu____9400 ->
                     let uu____9401 =
                       let uu____9407 =
                         let uu____9409 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9409
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9407)  in
                     FStar_Errors.raise_err uu____9401
                  in
               let uu____9427 = flatten1 t_head  in
               (match uu____9427 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9502 =
                          let uu____9508 =
                            let uu____9510 = FStar_Util.string_of_int n1  in
                            let uu____9512 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9514 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9510 uu____9512 uu____9514
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9508)
                           in
                        FStar_Errors.raise_err uu____9502)
                     else ();
                     (let uu____9520 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9520 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9573 args1 =
                            match uu____9573 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9673 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9673
                                 | (binders3,[]) ->
                                     let uu____9711 =
                                       let uu____9712 =
                                         let uu____9715 =
                                           let uu____9716 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9716
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9715
                                          in
                                       uu____9712.FStar_Syntax_Syntax.n  in
                                     (match uu____9711 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9749 =
                                            let uu____9750 =
                                              let uu____9751 =
                                                let uu____9766 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9766)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9751
                                               in
                                            mk1 uu____9750  in
                                          N uu____9749
                                      | uu____9779 -> failwith "wat?")
                                 | ([],uu____9781::uu____9782) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9835)::binders3,(arg,uu____9838)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9925 = FStar_List.splitAt n' binders1  in
                          (match uu____9925 with
                           | (binders2,uu____9959) ->
                               let uu____9992 =
                                 let uu____10015 =
                                   FStar_List.map2
                                     (fun uu____10077  ->
                                        fun uu____10078  ->
                                          match (uu____10077, uu____10078)
                                          with
                                          | ((bv,uu____10126),(arg,q)) ->
                                              let uu____10155 =
                                                let uu____10156 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____10156.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____10155 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____10177 ->
                                                   let uu____10178 =
                                                     let uu____10185 =
                                                       star_type' env arg  in
                                                     (uu____10185, q)  in
                                                   (uu____10178, [(arg, q)])
                                               | uu____10222 ->
                                                   let uu____10223 =
                                                     check_n env arg  in
                                                   (match uu____10223 with
                                                    | (uu____10248,s_arg,u_arg)
                                                        ->
                                                        let uu____10251 =
                                                          let uu____10260 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____10260
                                                          then
                                                            let uu____10271 =
                                                              let uu____10278
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____10278,
                                                                q)
                                                               in
                                                            [uu____10271;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____10251))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____10015  in
                               (match uu____9992 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10406 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10419 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10406, uu____10419)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10488) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10494) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10500,uu____10501) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10543 =
            let uu____10544 = env.tc_const c  in N uu____10544  in
          (uu____10543, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10551 ->
          let uu____10565 =
            let uu____10567 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10567  in
          failwith uu____10565
      | FStar_Syntax_Syntax.Tm_type uu____10576 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10584 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10606 ->
          let uu____10613 =
            let uu____10615 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10615  in
          failwith uu____10613
      | FStar_Syntax_Syntax.Tm_uvar uu____10624 ->
          let uu____10637 =
            let uu____10639 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10639  in
          failwith uu____10637
      | FStar_Syntax_Syntax.Tm_delayed uu____10648 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10678 =
            let uu____10680 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10680  in
          failwith uu____10678

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
          let uu____10729 = check_n env e0  in
          match uu____10729 with
          | (uu____10742,s_e0,u_e0) ->
              let uu____10745 =
                let uu____10774 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10835 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10835 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1140_10877 = env  in
                             let uu____10878 =
                               let uu____10879 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10879
                                in
                             {
                               tcenv = uu____10878;
                               subst = (uu___1140_10877.subst);
                               tc_const = (uu___1140_10877.tc_const)
                             }  in
                           let uu____10882 = f env1 body  in
                           (match uu____10882 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10954 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10774  in
              (match uu____10745 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____11060 = FStar_List.hd nms  in
                     match uu____11060 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_11069  ->
                          match uu___10_11069 with
                          | M uu____11071 -> true
                          | uu____11073 -> false) nms
                      in
                   let uu____11075 =
                     let uu____11112 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____11202  ->
                              match uu____11202 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11386 =
                                         check env original_body (M t2)  in
                                       (match uu____11386 with
                                        | (uu____11423,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11462,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____11112  in
                   (match uu____11075 with
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
                              (fun uu____11651  ->
                                 match uu____11651 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11702 =
                                         let uu____11703 =
                                           let uu____11720 =
                                             let uu____11731 =
                                               let uu____11740 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11743 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11740, uu____11743)  in
                                             [uu____11731]  in
                                           (s_body, uu____11720)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11703
                                          in
                                       mk1 uu____11702  in
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
                            let uu____11878 =
                              let uu____11879 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11879]  in
                            let uu____11898 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11878 uu____11898
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11922 =
                              let uu____11931 =
                                let uu____11938 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11938
                                 in
                              [uu____11931]  in
                            let uu____11957 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11922 uu____11957
                             in
                          let uu____11960 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11999 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11960, uu____11999)
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
                           let uu____12109 =
                             let uu____12110 =
                               let uu____12111 =
                                 let uu____12138 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____12138,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12111
                                in
                             mk1 uu____12110  in
                           let uu____12197 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____12109, uu____12197))))

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
              let uu____12262 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12262]  in
            let uu____12281 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12281 with
            | (x_binders1,e21) ->
                let uu____12294 = infer env e1  in
                (match uu____12294 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12311 = is_C t1  in
                       if uu____12311
                       then
                         let uu___1226_12314 = binding  in
                         let uu____12315 =
                           let uu____12318 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12318  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1226_12314.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1226_12314.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12315;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1226_12314.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1226_12314.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1226_12314.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1226_12314.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1229_12322 = env  in
                       let uu____12323 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1231_12325 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1231_12325.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1231_12325.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12323;
                         subst = (uu___1229_12322.subst);
                         tc_const = (uu___1229_12322.tc_const)
                       }  in
                     let uu____12326 = proceed env1 e21  in
                     (match uu____12326 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1238_12343 = binding  in
                            let uu____12344 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1238_12343.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1238_12343.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12344;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1238_12343.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1238_12343.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1238_12343.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1238_12343.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12347 =
                            let uu____12348 =
                              let uu____12349 =
                                let uu____12363 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1241_12380 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1241_12380.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1241_12380.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1241_12380.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1241_12380.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1241_12380.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1241_12380.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12363)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12349  in
                            mk1 uu____12348  in
                          let uu____12381 =
                            let uu____12382 =
                              let uu____12383 =
                                let uu____12397 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1243_12414 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1243_12414.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1243_12414.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1243_12414.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1243_12414.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1243_12414.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1243_12414.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12397)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12383  in
                            mk1 uu____12382  in
                          (nm_rec, uu____12347, uu____12381))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1250_12419 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1250_12419.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1250_12419.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1250_12419.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1250_12419.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1250_12419.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1253_12421 = env  in
                       let uu____12422 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1255_12424 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1255_12424.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1255_12424.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12422;
                         subst = (uu___1253_12421.subst);
                         tc_const = (uu___1253_12421.tc_const)
                       }  in
                     let uu____12425 = ensure_m env1 e21  in
                     (match uu____12425 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12449 =
                              let uu____12450 =
                                let uu____12467 =
                                  let uu____12478 =
                                    let uu____12487 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12490 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12487, uu____12490)  in
                                  [uu____12478]  in
                                (s_e2, uu____12467)  in
                              FStar_Syntax_Syntax.Tm_app uu____12450  in
                            mk1 uu____12449  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12532 =
                              let uu____12533 =
                                let uu____12550 =
                                  let uu____12561 =
                                    let uu____12570 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12570)  in
                                  [uu____12561]  in
                                (s_e1, uu____12550)  in
                              FStar_Syntax_Syntax.Tm_app uu____12533  in
                            mk1 uu____12532  in
                          let uu____12606 =
                            let uu____12607 =
                              let uu____12608 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12608]  in
                            FStar_Syntax_Util.abs uu____12607 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12627 =
                            let uu____12628 =
                              let uu____12629 =
                                let uu____12643 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1267_12660 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1267_12660.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1267_12660.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1267_12660.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1267_12660.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1267_12660.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1267_12660.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12643)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12629  in
                            mk1 uu____12628  in
                          ((M t2), uu____12606, uu____12627)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12670 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12670  in
      let uu____12671 = check env e mn  in
      match uu____12671 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12687 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12710 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12710  in
      let uu____12711 = check env e mn  in
      match uu____12711 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12727 -> failwith "[check_m]: impossible"

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
        (let uu____12760 =
           let uu____12762 = is_C c  in Prims.op_Negation uu____12762  in
         if uu____12760 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12776 =
           let uu____12777 = FStar_Syntax_Subst.compress c  in
           uu____12777.FStar_Syntax_Syntax.n  in
         match uu____12776 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12806 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12806 with
              | (wp_head,wp_args) ->
                  ((let uu____12850 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12869 =
                           let uu____12871 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12871
                            in
                         Prims.op_Negation uu____12869)
                       in
                    if uu____12850 then failwith "mismatch" else ());
                   (let uu____12884 =
                      let uu____12885 =
                        let uu____12902 =
                          FStar_List.map2
                            (fun uu____12940  ->
                               fun uu____12941  ->
                                 match (uu____12940, uu____12941) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____13003 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____13003
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____13012 =
                                         let uu____13014 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____13014 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____13012
                                       then
                                         let uu____13016 =
                                           let uu____13022 =
                                             let uu____13024 =
                                               print_implicit q  in
                                             let uu____13026 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____13024 uu____13026
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____13022)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____13016
                                       else ());
                                      (let uu____13032 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____13032, q)))) args wp_args
                           in
                        (head1, uu____12902)  in
                      FStar_Syntax_Syntax.Tm_app uu____12885  in
                    mk1 uu____12884)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____13078 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____13078 with
              | (binders_orig,comp1) ->
                  let uu____13085 =
                    let uu____13102 =
                      FStar_List.map
                        (fun uu____13142  ->
                           match uu____13142 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____13170 = is_C h  in
                               if uu____13170
                               then
                                 let w' =
                                   let uu____13186 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____13186
                                    in
                                 let uu____13188 =
                                   let uu____13197 =
                                     let uu____13206 =
                                       let uu____13213 =
                                         let uu____13214 =
                                           let uu____13215 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____13215  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____13214
                                          in
                                       (uu____13213, q)  in
                                     [uu____13206]  in
                                   (w', q) :: uu____13197  in
                                 (w', uu____13188)
                               else
                                 (let x =
                                    let uu____13249 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13249
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____13102  in
                  (match uu____13085 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13323 =
                           let uu____13326 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13326
                            in
                         FStar_Syntax_Subst.subst_comp uu____13323 comp1  in
                       let app =
                         let uu____13330 =
                           let uu____13331 =
                             let uu____13348 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13367 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13368 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13367, uu____13368)) bvs
                                in
                             (wp, uu____13348)  in
                           FStar_Syntax_Syntax.Tm_app uu____13331  in
                         mk1 uu____13330  in
                       let comp3 =
                         let uu____13383 = type_of_comp comp2  in
                         let uu____13384 = is_monadic_comp comp2  in
                         trans_G env uu____13383 uu____13384 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13387,uu____13388) ->
             trans_F_ env e wp
         | uu____13429 -> failwith "impossible trans_F_")

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
            let uu____13437 =
              let uu____13438 = star_type' env h  in
              let uu____13441 =
                let uu____13452 =
                  let uu____13461 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13461)  in
                [uu____13452]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13438;
                FStar_Syntax_Syntax.effect_args = uu____13441;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13437
          else
            (let uu____13487 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13487)

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
    fun t  -> let uu____13508 = n env.tcenv t  in star_type' env uu____13508
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13528 = n env.tcenv t  in check_n env uu____13528
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13545 = n env.tcenv c  in
        let uu____13546 = n env.tcenv wp  in
        trans_F_ env uu____13545 uu____13546
  