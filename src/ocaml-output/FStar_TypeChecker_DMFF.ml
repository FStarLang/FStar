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
                     | uu____216 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____218 = collect_binders rest  in
                   FStar_List.append bs uu____218
               | FStar_Syntax_Syntax.Tm_type uu____233 -> []
               | uu____240 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____267 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____267 FStar_Syntax_Util.name_binders
                in
             (let uu____293 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____293
              then
                let uu____297 =
                  let uu____299 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____299  in
                d uu____297
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____337 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____337 with
                | (sigelt,fv) ->
                    ((let uu____345 =
                        let uu____348 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____348
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____345);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____428  ->
                     match uu____428 with
                     | (t,b) ->
                         let uu____442 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____442))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____481 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____481))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____515 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____515)
                 in
              let uu____518 =
                let uu____535 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____560 =
                        let uu____563 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____563  in
                      FStar_Syntax_Util.arrow gamma uu____560  in
                    let uu____564 =
                      let uu____565 =
                        let uu____574 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____581 =
                          let uu____590 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____590]  in
                        uu____574 :: uu____581  in
                      FStar_List.append binders uu____565  in
                    FStar_Syntax_Util.abs uu____564 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____621 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____622 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____621, uu____622)  in
                match uu____535 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____664 =
                        let uu____665 =
                          let uu____682 =
                            let uu____693 =
                              FStar_List.map
                                (fun uu____715  ->
                                   match uu____715 with
                                   | (bv,uu____727) ->
                                       let uu____732 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____733 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____732, uu____733)) binders
                               in
                            let uu____735 =
                              let uu____742 =
                                let uu____747 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____748 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____747, uu____748)  in
                              let uu____750 =
                                let uu____757 =
                                  let uu____762 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____762)  in
                                [uu____757]  in
                              uu____742 :: uu____750  in
                            FStar_List.append uu____693 uu____735  in
                          (fv, uu____682)  in
                        FStar_Syntax_Syntax.Tm_app uu____665  in
                      mk1 uu____664  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____518 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____835 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____835
                       in
                    let ret1 =
                      let uu____840 =
                        let uu____841 =
                          let uu____844 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____844  in
                        FStar_Syntax_Util.residual_tot uu____841  in
                      FStar_Pervasives_Native.Some uu____840  in
                    let body =
                      let uu____848 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____848 ret1  in
                    let uu____851 =
                      let uu____852 = mk_all_implicit binders  in
                      let uu____859 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____852 uu____859  in
                    FStar_Syntax_Util.abs uu____851 body ret1  in
                  let c_pure1 =
                    let uu____897 = mk_lid "pure"  in
                    register env1 uu____897 c_pure  in
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
                      let uu____907 =
                        let uu____908 =
                          let uu____909 =
                            let uu____918 =
                              let uu____925 =
                                let uu____926 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____926
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____925  in
                            [uu____918]  in
                          let uu____939 =
                            let uu____942 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____942  in
                          FStar_Syntax_Util.arrow uu____909 uu____939  in
                        mk_gctx uu____908  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____907
                       in
                    let r =
                      let uu____945 =
                        let uu____946 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____946  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____945
                       in
                    let ret1 =
                      let uu____951 =
                        let uu____952 =
                          let uu____955 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____955  in
                        FStar_Syntax_Util.residual_tot uu____952  in
                      FStar_Pervasives_Native.Some uu____951  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____965 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____968 =
                          let uu____979 =
                            let uu____982 =
                              let uu____983 =
                                let uu____984 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____984
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____983  in
                            [uu____982]  in
                          FStar_List.append gamma_as_args uu____979  in
                        FStar_Syntax_Util.mk_app uu____965 uu____968  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____987 =
                      let uu____988 = mk_all_implicit binders  in
                      let uu____995 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____988 uu____995  in
                    FStar_Syntax_Util.abs uu____987 outer_body ret1  in
                  let c_app1 =
                    let uu____1047 = mk_lid "app"  in
                    register env1 uu____1047 c_app  in
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
                      let uu____1059 =
                        let uu____1068 =
                          let uu____1075 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1075  in
                        [uu____1068]  in
                      let uu____1088 =
                        let uu____1091 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1091  in
                      FStar_Syntax_Util.arrow uu____1059 uu____1088  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1095 =
                        let uu____1096 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1096  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1095
                       in
                    let ret1 =
                      let uu____1101 =
                        let uu____1102 =
                          let uu____1105 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1105  in
                        FStar_Syntax_Util.residual_tot uu____1102  in
                      FStar_Pervasives_Native.Some uu____1101  in
                    let uu____1106 =
                      let uu____1107 = mk_all_implicit binders  in
                      let uu____1114 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1107 uu____1114  in
                    let uu____1165 =
                      let uu____1168 =
                        let uu____1179 =
                          let uu____1182 =
                            let uu____1183 =
                              let uu____1194 =
                                let uu____1197 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1197]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1194
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1183  in
                          let uu____1206 =
                            let uu____1209 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1209]  in
                          uu____1182 :: uu____1206  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1179
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1168  in
                    FStar_Syntax_Util.abs uu____1106 uu____1165 ret1  in
                  let c_lift11 =
                    let uu____1219 = mk_lid "lift1"  in
                    register env1 uu____1219 c_lift1  in
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
                      let uu____1233 =
                        let uu____1242 =
                          let uu____1249 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1249  in
                        let uu____1250 =
                          let uu____1259 =
                            let uu____1266 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1266  in
                          [uu____1259]  in
                        uu____1242 :: uu____1250  in
                      let uu____1285 =
                        let uu____1288 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1288  in
                      FStar_Syntax_Util.arrow uu____1233 uu____1285  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1292 =
                        let uu____1293 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1293  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1292
                       in
                    let a2 =
                      let uu____1296 =
                        let uu____1297 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1297  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1296
                       in
                    let ret1 =
                      let uu____1302 =
                        let uu____1303 =
                          let uu____1306 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1306  in
                        FStar_Syntax_Util.residual_tot uu____1303  in
                      FStar_Pervasives_Native.Some uu____1302  in
                    let uu____1307 =
                      let uu____1308 = mk_all_implicit binders  in
                      let uu____1315 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1308 uu____1315  in
                    let uu____1380 =
                      let uu____1383 =
                        let uu____1394 =
                          let uu____1397 =
                            let uu____1398 =
                              let uu____1409 =
                                let uu____1412 =
                                  let uu____1413 =
                                    let uu____1424 =
                                      let uu____1427 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1427]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1424
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1413
                                   in
                                let uu____1436 =
                                  let uu____1439 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1439]  in
                                uu____1412 :: uu____1436  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1409
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1398  in
                          let uu____1448 =
                            let uu____1451 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1451]  in
                          uu____1397 :: uu____1448  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1394
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1383  in
                    FStar_Syntax_Util.abs uu____1307 uu____1380 ret1  in
                  let c_lift21 =
                    let uu____1461 = mk_lid "lift2"  in
                    register env1 uu____1461 c_lift2  in
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
                      let uu____1473 =
                        let uu____1482 =
                          let uu____1489 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1489  in
                        [uu____1482]  in
                      let uu____1502 =
                        let uu____1505 =
                          let uu____1506 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1506  in
                        FStar_Syntax_Syntax.mk_Total uu____1505  in
                      FStar_Syntax_Util.arrow uu____1473 uu____1502  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1512 =
                        let uu____1513 =
                          let uu____1516 =
                            let uu____1517 =
                              let uu____1526 =
                                let uu____1533 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1533
                                 in
                              [uu____1526]  in
                            let uu____1546 =
                              let uu____1549 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1549  in
                            FStar_Syntax_Util.arrow uu____1517 uu____1546  in
                          mk_ctx uu____1516  in
                        FStar_Syntax_Util.residual_tot uu____1513  in
                      FStar_Pervasives_Native.Some uu____1512  in
                    let e1 =
                      let uu____1551 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1551
                       in
                    let body =
                      let uu____1556 =
                        let uu____1557 =
                          let uu____1566 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1566]  in
                        FStar_List.append gamma uu____1557  in
                      let uu____1591 =
                        let uu____1594 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1597 =
                          let uu____1608 =
                            let uu____1609 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1609  in
                          let uu____1610 = args_of_binders1 gamma  in
                          uu____1608 :: uu____1610  in
                        FStar_Syntax_Util.mk_app uu____1594 uu____1597  in
                      FStar_Syntax_Util.abs uu____1556 uu____1591 ret1  in
                    let uu____1613 =
                      let uu____1614 = mk_all_implicit binders  in
                      let uu____1621 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1614 uu____1621  in
                    FStar_Syntax_Util.abs uu____1613 body ret1  in
                  let c_push1 =
                    let uu____1666 = mk_lid "push"  in
                    register env1 uu____1666 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > Prims.int_zero
                    then
                      let uu____1693 =
                        let uu____1694 =
                          let uu____1711 = args_of_binders1 binders  in
                          (c, uu____1711)  in
                        FStar_Syntax_Syntax.Tm_app uu____1694  in
                      mk1 uu____1693
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1740 =
                        let uu____1741 =
                          let uu____1750 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1757 =
                            let uu____1766 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1766]  in
                          uu____1750 :: uu____1757  in
                        let uu____1791 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1741 uu____1791  in
                      FStar_Syntax_Syntax.mk_Total uu____1740  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1796 =
                      let uu____1797 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1797  in
                    let uu____1812 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.of_int (2))) FStar_Pervasives_Native.None
                         in
                      let uu____1817 =
                        let uu____1820 =
                          let uu____1831 =
                            let uu____1834 =
                              let uu____1835 =
                                let uu____1846 =
                                  let uu____1855 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1855  in
                                [uu____1846]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1835  in
                            [uu____1834]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1831
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1820  in
                      FStar_Syntax_Util.ascribe uu____1817
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1796 uu____1812
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1899 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1899 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1912 =
                        let uu____1921 =
                          let uu____1928 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1928  in
                        [uu____1921]  in
                      let uu____1941 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1912 uu____1941  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1949 =
                        let uu____1960 =
                          let uu____1963 =
                            let uu____1964 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1964  in
                          let uu____1983 =
                            let uu____1986 =
                              let uu____1987 =
                                let uu____1998 =
                                  let uu____2001 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2001]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1998
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1987  in
                            [uu____1986]  in
                          uu____1963 :: uu____1983  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1960
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1949  in
                    let uu____2018 =
                      let uu____2019 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2019  in
                    FStar_Syntax_Util.abs uu____2018 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2035 = mk_lid "wp_close"  in
                    register env1 uu____2035 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2046 =
                      let uu____2047 =
                        let uu____2048 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left
                          FStar_TypeChecker_Common.lcomp_of_comp uu____2048
                         in
                      FStar_TypeChecker_Common.residual_comp_of_lcomp
                        uu____2047
                       in
                    FStar_Pervasives_Native.Some uu____2046  in
                  let mk_forall1 x body =
                    let uu____2060 =
                      let uu____2067 =
                        let uu____2068 =
                          let uu____2085 =
                            let uu____2096 =
                              let uu____2105 =
                                let uu____2106 =
                                  let uu____2107 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2107]  in
                                FStar_Syntax_Util.abs uu____2106 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2105  in
                            [uu____2096]  in
                          (FStar_Syntax_Util.tforall, uu____2085)  in
                        FStar_Syntax_Syntax.Tm_app uu____2068  in
                      FStar_Syntax_Syntax.mk uu____2067  in
                    uu____2060 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2165 =
                      let uu____2166 = FStar_Syntax_Subst.compress t  in
                      uu____2166.FStar_Syntax_Syntax.n  in
                    match uu____2165 with
                    | FStar_Syntax_Syntax.Tm_type uu____2170 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2203  ->
                              match uu____2203 with
                              | (b,uu____2212) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2217 -> true  in
                  let rec is_monotonic t =
                    let uu____2230 =
                      let uu____2231 = FStar_Syntax_Subst.compress t  in
                      uu____2231.FStar_Syntax_Syntax.n  in
                    match uu____2230 with
                    | FStar_Syntax_Syntax.Tm_type uu____2235 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2268  ->
                              match uu____2268 with
                              | (b,uu____2277) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2282 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2356 =
                      let uu____2357 = FStar_Syntax_Subst.compress t1  in
                      uu____2357.FStar_Syntax_Syntax.n  in
                    match uu____2356 with
                    | FStar_Syntax_Syntax.Tm_type uu____2362 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2365);
                                      FStar_Syntax_Syntax.pos = uu____2366;
                                      FStar_Syntax_Syntax.vars = uu____2367;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2411 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2411
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2421 =
                              let uu____2424 =
                                let uu____2435 =
                                  let uu____2444 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2444  in
                                [uu____2435]  in
                              FStar_Syntax_Util.mk_app x uu____2424  in
                            let uu____2461 =
                              let uu____2464 =
                                let uu____2475 =
                                  let uu____2484 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2484  in
                                [uu____2475]  in
                              FStar_Syntax_Util.mk_app y uu____2464  in
                            mk_rel1 b uu____2421 uu____2461  in
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
                             let uu____2508 =
                               let uu____2511 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2514 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2511 uu____2514  in
                             let uu____2517 =
                               let uu____2520 =
                                 let uu____2523 =
                                   let uu____2534 =
                                     let uu____2543 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2543
                                      in
                                   [uu____2534]  in
                                 FStar_Syntax_Util.mk_app x uu____2523  in
                               let uu____2560 =
                                 let uu____2563 =
                                   let uu____2574 =
                                     let uu____2583 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2583
                                      in
                                   [uu____2574]  in
                                 FStar_Syntax_Util.mk_app y uu____2563  in
                               mk_rel1 b uu____2520 uu____2560  in
                             FStar_Syntax_Util.mk_imp uu____2508 uu____2517
                              in
                           let uu____2600 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2600)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2603);
                                      FStar_Syntax_Syntax.pos = uu____2604;
                                      FStar_Syntax_Syntax.vars = uu____2605;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2649 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2649
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2659 =
                              let uu____2662 =
                                let uu____2673 =
                                  let uu____2682 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2682  in
                                [uu____2673]  in
                              FStar_Syntax_Util.mk_app x uu____2662  in
                            let uu____2699 =
                              let uu____2702 =
                                let uu____2713 =
                                  let uu____2722 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2722  in
                                [uu____2713]  in
                              FStar_Syntax_Util.mk_app y uu____2702  in
                            mk_rel1 b uu____2659 uu____2699  in
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
                             let uu____2746 =
                               let uu____2749 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2752 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2749 uu____2752  in
                             let uu____2755 =
                               let uu____2758 =
                                 let uu____2761 =
                                   let uu____2772 =
                                     let uu____2781 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2781
                                      in
                                   [uu____2772]  in
                                 FStar_Syntax_Util.mk_app x uu____2761  in
                               let uu____2798 =
                                 let uu____2801 =
                                   let uu____2812 =
                                     let uu____2821 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2821
                                      in
                                   [uu____2812]  in
                                 FStar_Syntax_Util.mk_app y uu____2801  in
                               mk_rel1 b uu____2758 uu____2798  in
                             FStar_Syntax_Util.mk_imp uu____2746 uu____2755
                              in
                           let uu____2838 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2838)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___228_2877 = t1  in
                          let uu____2878 =
                            let uu____2879 =
                              let uu____2894 =
                                let uu____2897 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2897  in
                              ([binder], uu____2894)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2879  in
                          {
                            FStar_Syntax_Syntax.n = uu____2878;
                            FStar_Syntax_Syntax.pos =
                              (uu___228_2877.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___228_2877.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2920 ->
                        failwith "unhandled arrow"
                    | uu____2938 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____2975 =
                        let uu____2976 = FStar_Syntax_Subst.compress t1  in
                        uu____2976.FStar_Syntax_Syntax.n  in
                      match uu____2975 with
                      | FStar_Syntax_Syntax.Tm_type uu____2979 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3006 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3006
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3027 =
                                let uu____3028 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3028 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3027
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   Prims.int_one)
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3058 =
                            let uu____3069 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3087  ->
                                     match uu____3087 with
                                     | (t2,q) ->
                                         let uu____3107 = project i x  in
                                         let uu____3110 = project i y  in
                                         mk_stronger t2 uu____3107 uu____3110)
                                args
                               in
                            match uu____3069 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3058 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3164);
                                      FStar_Syntax_Syntax.pos = uu____3165;
                                      FStar_Syntax_Syntax.vars = uu____3166;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3210  ->
                                   match uu____3210 with
                                   | (bv,q) ->
                                       let uu____3224 =
                                         let uu____3226 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3226  in
                                       FStar_Syntax_Syntax.gen_bv uu____3224
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3235 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3235) bvs
                             in
                          let body =
                            let uu____3237 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3240 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3237 uu____3240  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3249);
                                      FStar_Syntax_Syntax.pos = uu____3250;
                                      FStar_Syntax_Syntax.vars = uu____3251;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3295  ->
                                   match uu____3295 with
                                   | (bv,q) ->
                                       let uu____3309 =
                                         let uu____3311 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3311  in
                                       FStar_Syntax_Syntax.gen_bv uu____3309
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3320 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3320) bvs
                             in
                          let body =
                            let uu____3322 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3325 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3322 uu____3325  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3332 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3335 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3338 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3341 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3335 uu____3338 uu____3341  in
                    let uu____3344 =
                      let uu____3345 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3345  in
                    FStar_Syntax_Util.abs uu____3344 body ret_tot_type  in
                  let stronger1 =
                    let uu____3387 = mk_lid "stronger"  in
                    register env1 uu____3387 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3395 = FStar_Util.prefix gamma  in
                    match uu____3395 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3461 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3461
                             in
                          let uu____3466 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3466 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3476 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3476  in
                              let guard_free1 =
                                let uu____3488 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3488  in
                              let pat =
                                let uu____3492 =
                                  let uu____3503 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3503]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3492
                                 in
                              let pattern_guarded_body =
                                let uu____3531 =
                                  let uu____3532 =
                                    let uu____3539 =
                                      let uu____3540 =
                                        let uu____3561 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1
                                           in
                                        let uu____3566 =
                                          let uu____3579 =
                                            let uu____3590 =
                                              FStar_Syntax_Syntax.as_arg pat
                                               in
                                            [uu____3590]  in
                                          [uu____3579]  in
                                        (uu____3561, uu____3566)  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3540
                                       in
                                    (body, uu____3539)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3532  in
                                mk1 uu____3531  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3653 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3662 =
                            let uu____3665 =
                              let uu____3666 =
                                let uu____3669 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3672 =
                                  let uu____3683 = args_of_binders1 wp_args
                                     in
                                  let uu____3686 =
                                    let uu____3689 =
                                      let uu____3690 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3690
                                       in
                                    [uu____3689]  in
                                  FStar_List.append uu____3683 uu____3686  in
                                FStar_Syntax_Util.mk_app uu____3669
                                  uu____3672
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3666  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3665
                             in
                          FStar_Syntax_Util.abs gamma uu____3662
                            ret_gtot_type
                           in
                        let uu____3691 =
                          let uu____3692 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3692  in
                        FStar_Syntax_Util.abs uu____3691 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3708 = mk_lid "ite_wp"  in
                    register env1 uu____3708 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3716 = FStar_Util.prefix gamma  in
                    match uu____3716 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3774 =
                            let uu____3775 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3782 =
                              let uu____3793 =
                                let uu____3802 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3802  in
                              [uu____3793]  in
                            FStar_Syntax_Util.mk_app uu____3775 uu____3782
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3774
                           in
                        let uu____3819 =
                          let uu____3820 =
                            let uu____3829 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3829 gamma  in
                          FStar_List.append binders uu____3820  in
                        FStar_Syntax_Util.abs uu____3819 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3851 = mk_lid "null_wp"  in
                    register env1 uu____3851 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3864 =
                        let uu____3875 =
                          let uu____3878 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3879 =
                            let uu____3882 =
                              let uu____3883 =
                                let uu____3894 =
                                  let uu____3903 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3903  in
                                [uu____3894]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3883
                               in
                            let uu____3920 =
                              let uu____3923 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3923]  in
                            uu____3882 :: uu____3920  in
                          uu____3878 :: uu____3879  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3875
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3864  in
                    let uu____3932 =
                      let uu____3933 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3933  in
                    FStar_Syntax_Util.abs uu____3932 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3949 = mk_lid "wp_trivial"  in
                    register env1 uu____3949 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3955 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3955
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let ed_combs =
                      match ed.FStar_Syntax_Syntax.combinators with
                      | FStar_Syntax_Syntax.DM4F_eff combs ->
                          let uu____3969 =
                            let uu___337_3970 = combs  in
                            let uu____3971 =
                              let uu____3972 = c stronger2  in
                              ([], uu____3972)  in
                            let uu____3979 =
                              let uu____3980 = c wp_if_then_else2  in
                              ([], uu____3980)  in
                            let uu____3987 =
                              let uu____3988 = c ite_wp2  in ([], uu____3988)
                               in
                            let uu____3995 =
                              let uu____3996 = c wp_close2  in
                              ([], uu____3996)  in
                            let uu____4003 =
                              let uu____4004 = c wp_trivial2  in
                              ([], uu____4004)  in
                            {
                              FStar_Syntax_Syntax.ret_wp =
                                (uu___337_3970.FStar_Syntax_Syntax.ret_wp);
                              FStar_Syntax_Syntax.bind_wp =
                                (uu___337_3970.FStar_Syntax_Syntax.bind_wp);
                              FStar_Syntax_Syntax.stronger = uu____3971;
                              FStar_Syntax_Syntax.if_then_else = uu____3979;
                              FStar_Syntax_Syntax.ite_wp = uu____3987;
                              FStar_Syntax_Syntax.close_wp = uu____3995;
                              FStar_Syntax_Syntax.trivial = uu____4003;
                              FStar_Syntax_Syntax.repr =
                                (uu___337_3970.FStar_Syntax_Syntax.repr);
                              FStar_Syntax_Syntax.return_repr =
                                (uu___337_3970.FStar_Syntax_Syntax.return_repr);
                              FStar_Syntax_Syntax.bind_repr =
                                (uu___337_3970.FStar_Syntax_Syntax.bind_repr)
                            }  in
                          FStar_Syntax_Syntax.DM4F_eff uu____3969
                      | uu____4011 ->
                          failwith
                            "Impossible! For a DM4F effect combinators must be in DM4f_eff"
                       in
                    let uu____4013 =
                      let uu____4014 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4014  in
                    (uu____4013,
                      (let uu___341_4041 = ed  in
                       {
                         FStar_Syntax_Syntax.mname =
                           (uu___341_4041.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___341_4041.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.univs =
                           (uu___341_4041.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___341_4041.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature =
                           (uu___341_4041.FStar_Syntax_Syntax.signature);
                         FStar_Syntax_Syntax.combinators = ed_combs;
                         FStar_Syntax_Syntax.actions =
                           (uu___341_4041.FStar_Syntax_Syntax.actions);
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___341_4041.FStar_Syntax_Syntax.eff_attrs)
                       }))))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___346_4059 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___346_4059.subst);
        tc_const = (uu___346_4059.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4080 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4099 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4119) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4133  ->
                match uu___0_4133 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4136 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4138 ->
        let uu____4139 =
          let uu____4145 =
            let uu____4147 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4147
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4145)  in
        FStar_Errors.raise_error uu____4139 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4157  ->
    match uu___1_4157 with
    | N t ->
        let uu____4160 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4160
    | M t ->
        let uu____4164 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4164
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4173,c) -> nm_of_comp c
    | uu____4195 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4208 = nm_of_comp c  in
    match uu____4208 with | M uu____4210 -> true | N uu____4212 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4223 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4239 =
        let uu____4248 =
          let uu____4255 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4255  in
        [uu____4248]  in
      let uu____4274 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4239 uu____4274  in
    let uu____4277 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4277
  
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
        let uu____4319 =
          let uu____4320 =
            let uu____4335 =
              let uu____4344 =
                let uu____4351 =
                  let uu____4352 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4352  in
                let uu____4353 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4351, uu____4353)  in
              [uu____4344]  in
            let uu____4371 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4335, uu____4371)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4320  in
        mk1 uu____4319

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4411) ->
          let binders1 =
            FStar_List.map
              (fun uu____4457  ->
                 match uu____4457 with
                 | (bv,aqual) ->
                     let uu____4476 =
                       let uu___396_4477 = bv  in
                       let uu____4478 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___396_4477.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___396_4477.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4478
                       }  in
                     (uu____4476, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4483,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4485);
                             FStar_Syntax_Syntax.pos = uu____4486;
                             FStar_Syntax_Syntax.vars = uu____4487;_})
               ->
               let uu____4516 =
                 let uu____4517 =
                   let uu____4532 =
                     let uu____4535 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4535  in
                   (binders1, uu____4532)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4517  in
               mk1 uu____4516
           | uu____4546 ->
               let uu____4547 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4547 with
                | N hn ->
                    let uu____4549 =
                      let uu____4550 =
                        let uu____4565 =
                          let uu____4568 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4568  in
                        (binders1, uu____4565)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4550  in
                    mk1 uu____4549
                | M a ->
                    let uu____4580 =
                      let uu____4581 =
                        let uu____4596 =
                          let uu____4605 =
                            let uu____4614 =
                              let uu____4621 =
                                let uu____4622 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4622  in
                              let uu____4623 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4621, uu____4623)  in
                            [uu____4614]  in
                          FStar_List.append binders1 uu____4605  in
                        let uu____4647 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4596, uu____4647)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4581  in
                    mk1 uu____4580))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4741 = f x  in
                    FStar_Util.string_builder_append strb uu____4741);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4750 = f x1  in
                         FStar_Util.string_builder_append strb uu____4750))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4754 =
              let uu____4760 =
                let uu____4762 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4764 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4762 uu____4764
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4760)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4754  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4786 =
              let uu____4787 = FStar_Syntax_Subst.compress ty  in
              uu____4787.FStar_Syntax_Syntax.n  in
            match uu____4786 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4813 =
                  let uu____4815 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4815  in
                if uu____4813
                then false
                else
                  (try
                     (fun uu___445_4832  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4856 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4856 s  in
                              let uu____4859 =
                                let uu____4861 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4861  in
                              if uu____4859
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4867 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4867 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4892  ->
                                          match uu____4892 with
                                          | (bv,uu____4904) ->
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
            | uu____4932 ->
                ((let uu____4934 =
                    let uu____4940 =
                      let uu____4942 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4942
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4940)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4934);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4958 =
              let uu____4959 = FStar_Syntax_Subst.compress head2  in
              uu____4959.FStar_Syntax_Syntax.n  in
            match uu____4958 with
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
                  (let uu____4965 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4965)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4968 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4968 with
                 | ((uu____4978,ty),uu____4980) ->
                     let uu____4985 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4985
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____4998 =
                         let uu____4999 = FStar_Syntax_Subst.compress res  in
                         uu____4999.FStar_Syntax_Syntax.n  in
                       (match uu____4998 with
                        | FStar_Syntax_Syntax.Tm_app uu____5003 -> true
                        | uu____5021 ->
                            ((let uu____5023 =
                                let uu____5029 =
                                  let uu____5031 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5031
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5029)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5023);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5039 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5041 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5044) ->
                is_valid_application t2
            | uu____5049 -> false  in
          let uu____5051 = is_valid_application head1  in
          if uu____5051
          then
            let uu____5054 =
              let uu____5055 =
                let uu____5072 =
                  FStar_List.map
                    (fun uu____5101  ->
                       match uu____5101 with
                       | (t2,qual) ->
                           let uu____5126 = star_type' env t2  in
                           (uu____5126, qual)) args
                   in
                (head1, uu____5072)  in
              FStar_Syntax_Syntax.Tm_app uu____5055  in
            mk1 uu____5054
          else
            (let uu____5143 =
               let uu____5149 =
                 let uu____5151 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5151
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5149)  in
             FStar_Errors.raise_err uu____5143)
      | FStar_Syntax_Syntax.Tm_bvar uu____5155 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5156 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5157 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5158 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5186 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5186 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___517_5194 = env  in
                 let uu____5195 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5195;
                   subst = (uu___517_5194.subst);
                   tc_const = (uu___517_5194.tc_const)
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
               ((let uu___532_5222 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___532_5222.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___532_5222.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5229 =
            let uu____5230 =
              let uu____5237 = star_type' env t2  in (uu____5237, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5230  in
          mk1 uu____5229
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5289 =
            let uu____5290 =
              let uu____5317 = star_type' env e  in
              let uu____5320 =
                let uu____5337 =
                  let uu____5346 = star_type' env t2  in
                  FStar_Util.Inl uu____5346  in
                (uu____5337, FStar_Pervasives_Native.None)  in
              (uu____5317, uu____5320, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5290  in
          mk1 uu____5289
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5434 =
            let uu____5435 =
              let uu____5462 = star_type' env e  in
              let uu____5465 =
                let uu____5482 =
                  let uu____5491 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5491  in
                (uu____5482, FStar_Pervasives_Native.None)  in
              (uu____5462, uu____5465, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5435  in
          mk1 uu____5434
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5532,(uu____5533,FStar_Pervasives_Native.Some uu____5534),uu____5535)
          ->
          let uu____5584 =
            let uu____5590 =
              let uu____5592 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5592
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5590)  in
          FStar_Errors.raise_err uu____5584
      | FStar_Syntax_Syntax.Tm_refine uu____5596 ->
          let uu____5603 =
            let uu____5609 =
              let uu____5611 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5611
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5609)  in
          FStar_Errors.raise_err uu____5603
      | FStar_Syntax_Syntax.Tm_uinst uu____5615 ->
          let uu____5622 =
            let uu____5628 =
              let uu____5630 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5630
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5628)  in
          FStar_Errors.raise_err uu____5622
      | FStar_Syntax_Syntax.Tm_quoted uu____5634 ->
          let uu____5641 =
            let uu____5647 =
              let uu____5649 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5649
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5647)  in
          FStar_Errors.raise_err uu____5641
      | FStar_Syntax_Syntax.Tm_constant uu____5653 ->
          let uu____5654 =
            let uu____5660 =
              let uu____5662 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5662
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5660)  in
          FStar_Errors.raise_err uu____5654
      | FStar_Syntax_Syntax.Tm_match uu____5666 ->
          let uu____5689 =
            let uu____5695 =
              let uu____5697 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5697
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5695)  in
          FStar_Errors.raise_err uu____5689
      | FStar_Syntax_Syntax.Tm_let uu____5701 ->
          let uu____5715 =
            let uu____5721 =
              let uu____5723 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5723
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5721)  in
          FStar_Errors.raise_err uu____5715
      | FStar_Syntax_Syntax.Tm_uvar uu____5727 ->
          let uu____5740 =
            let uu____5746 =
              let uu____5748 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5748
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5746)  in
          FStar_Errors.raise_err uu____5740
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5752 =
            let uu____5758 =
              let uu____5760 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5760
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5758)  in
          FStar_Errors.raise_err uu____5752
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5765 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5765
      | FStar_Syntax_Syntax.Tm_delayed uu____5768 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_5800  ->
    match uu___3_5800 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_5811  ->
                match uu___2_5811 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5814 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5824 =
      let uu____5825 = FStar_Syntax_Subst.compress t  in
      uu____5825.FStar_Syntax_Syntax.n  in
    match uu____5824 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5857 =
            let uu____5858 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5858  in
          is_C uu____5857  in
        if r
        then
          ((let uu____5882 =
              let uu____5884 =
                FStar_List.for_all
                  (fun uu____5895  ->
                     match uu____5895 with | (h,uu____5904) -> is_C h) args
                 in
              Prims.op_Negation uu____5884  in
            if uu____5882 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5917 =
              let uu____5919 =
                FStar_List.for_all
                  (fun uu____5931  ->
                     match uu____5931 with
                     | (h,uu____5940) ->
                         let uu____5945 = is_C h  in
                         Prims.op_Negation uu____5945) args
                 in
              Prims.op_Negation uu____5919  in
            if uu____5917 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5974 = nm_of_comp comp  in
        (match uu____5974 with
         | M t1 ->
             ((let uu____5978 = is_C t1  in
               if uu____5978 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5987) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5993) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5999,uu____6000) -> is_C t1
    | uu____6041 -> false
  
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
          let uu____6077 =
            let uu____6078 =
              let uu____6095 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6098 =
                let uu____6109 =
                  let uu____6118 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6118)  in
                [uu____6109]  in
              (uu____6095, uu____6098)  in
            FStar_Syntax_Syntax.Tm_app uu____6078  in
          mk1 uu____6077  in
        let uu____6154 =
          let uu____6155 = FStar_Syntax_Syntax.mk_binder p  in [uu____6155]
           in
        FStar_Syntax_Util.abs uu____6154 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6180  ->
    match uu___4_6180 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6183 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6421 =
          match uu____6421 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6458 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6461 =
                       let uu____6463 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6463  in
                     Prims.op_Negation uu____6461)
                   in
                if uu____6458
                then
                  let uu____6465 =
                    let uu____6471 =
                      let uu____6473 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6475 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6477 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6473 uu____6475 uu____6477
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6471)  in
                  FStar_Errors.raise_err uu____6465
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6502 = mk_return env t1 s_e  in
                     ((M t1), uu____6502, u_e)))
               | (M t1,N t2) ->
                   let uu____6509 =
                     let uu____6515 =
                       let uu____6517 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6519 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6521 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6517 uu____6519 uu____6521
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6515)
                      in
                   FStar_Errors.raise_err uu____6509)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_6573 =
            match uu___5_6573 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6589 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6610 =
                let uu____6616 =
                  let uu____6618 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6618
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6616)  in
              FStar_Errors.raise_error uu____6610 e2.FStar_Syntax_Syntax.pos
          | M uu____6628 ->
              let uu____6629 = check env1 e2 context_nm  in
              strip_m uu____6629
           in
        let uu____6636 =
          let uu____6637 = FStar_Syntax_Subst.compress e  in
          uu____6637.FStar_Syntax_Syntax.n  in
        match uu____6636 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6646 ->
            let uu____6647 = infer env e  in return_if uu____6647
        | FStar_Syntax_Syntax.Tm_name uu____6654 ->
            let uu____6655 = infer env e  in return_if uu____6655
        | FStar_Syntax_Syntax.Tm_fvar uu____6662 ->
            let uu____6663 = infer env e  in return_if uu____6663
        | FStar_Syntax_Syntax.Tm_abs uu____6670 ->
            let uu____6689 = infer env e  in return_if uu____6689
        | FStar_Syntax_Syntax.Tm_constant uu____6696 ->
            let uu____6697 = infer env e  in return_if uu____6697
        | FStar_Syntax_Syntax.Tm_quoted uu____6704 ->
            let uu____6711 = infer env e  in return_if uu____6711
        | FStar_Syntax_Syntax.Tm_app uu____6718 ->
            let uu____6735 = infer env e  in return_if uu____6735
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6743 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6743 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6808) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6814) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6820,uu____6821) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6862 ->
            let uu____6876 =
              let uu____6878 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6878  in
            failwith uu____6876
        | FStar_Syntax_Syntax.Tm_type uu____6887 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6895 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6917 ->
            let uu____6924 =
              let uu____6926 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6926  in
            failwith uu____6924
        | FStar_Syntax_Syntax.Tm_uvar uu____6935 ->
            let uu____6948 =
              let uu____6950 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6950  in
            failwith uu____6948
        | FStar_Syntax_Syntax.Tm_delayed uu____6959 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6989 =
              let uu____6991 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6991  in
            failwith uu____6989

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
      let uu____7021 =
        let uu____7022 = FStar_Syntax_Subst.compress e  in
        uu____7022.FStar_Syntax_Syntax.n  in
      match uu____7021 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7041 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7041
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7092;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7093;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7099 =
                  let uu___767_7100 = rc  in
                  let uu____7101 =
                    let uu____7106 =
                      let uu____7109 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7109  in
                    FStar_Pervasives_Native.Some uu____7106  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___767_7100.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7101;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___767_7100.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7099
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___773_7121 = env  in
            let uu____7122 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7122;
              subst = (uu___773_7121.subst);
              tc_const = (uu___773_7121.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7148  ->
                 match uu____7148 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___780_7171 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___780_7171.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___780_7171.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7172 =
            FStar_List.fold_left
              (fun uu____7203  ->
                 fun uu____7204  ->
                   match (uu____7203, uu____7204) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7262 = is_C c  in
                       if uu____7262
                       then
                         let xw =
                           let uu____7272 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7272
                            in
                         let x =
                           let uu___792_7275 = bv  in
                           let uu____7276 =
                             let uu____7279 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7279  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___792_7275.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___792_7275.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7276
                           }  in
                         let env3 =
                           let uu___795_7281 = env2  in
                           let uu____7282 =
                             let uu____7285 =
                               let uu____7286 =
                                 let uu____7293 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7293)  in
                               FStar_Syntax_Syntax.NT uu____7286  in
                             uu____7285 :: (env2.subst)  in
                           {
                             tcenv = (uu___795_7281.tcenv);
                             subst = uu____7282;
                             tc_const = (uu___795_7281.tc_const)
                           }  in
                         let uu____7298 =
                           let uu____7301 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7302 =
                             let uu____7305 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7305 :: acc  in
                           uu____7301 :: uu____7302  in
                         (env3, uu____7298)
                       else
                         (let x =
                            let uu___798_7311 = bv  in
                            let uu____7312 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___798_7311.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___798_7311.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7312
                            }  in
                          let uu____7315 =
                            let uu____7318 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7318 :: acc  in
                          (env2, uu____7315))) (env1, []) binders1
             in
          (match uu____7172 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7338 =
                 let check_what =
                   let uu____7364 = is_monadic rc_opt1  in
                   if uu____7364 then check_m else check_n  in
                 let uu____7381 = check_what env2 body1  in
                 match uu____7381 with
                 | (t,s_body,u_body) ->
                     let uu____7401 =
                       let uu____7404 =
                         let uu____7405 = is_monadic rc_opt1  in
                         if uu____7405 then M t else N t  in
                       comp_of_nm uu____7404  in
                     (uu____7401, s_body, u_body)
                  in
               (match uu____7338 with
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
                                 let uu____7445 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7451  ->
                                           match uu___6_7451 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7454 -> false))
                                    in
                                 if uu____7445
                                 then
                                   let uu____7457 =
                                     FStar_List.filter
                                       (fun uu___7_7461  ->
                                          match uu___7_7461 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7464 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7457
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7475 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7481  ->
                                         match uu___8_7481 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7484 -> false))
                                  in
                               if uu____7475
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7493  ->
                                        match uu___9_7493 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7496 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7498 =
                                   let uu____7499 =
                                     let uu____7504 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7504
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7499 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7498
                               else
                                 (let uu____7511 =
                                    let uu___839_7512 = rc  in
                                    let uu____7513 =
                                      let uu____7518 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7518
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___839_7512.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7513;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___839_7512.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7511))
                       in
                    let uu____7523 =
                      let comp1 =
                        let uu____7531 = is_monadic rc_opt1  in
                        let uu____7533 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7531 uu____7533
                         in
                      let uu____7534 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7534,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7523 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7572 =
                             let uu____7573 =
                               let uu____7592 =
                                 let uu____7595 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7595 s_rc_opt  in
                               (s_binders1, s_body1, uu____7592)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7573  in
                           mk1 uu____7572  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7615 =
                             let uu____7616 =
                               let uu____7635 =
                                 let uu____7638 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7638 u_rc_opt  in
                               (u_binders2, u_body2, uu____7635)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7616  in
                           mk1 uu____7615  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7654;_};
            FStar_Syntax_Syntax.fv_delta = uu____7655;
            FStar_Syntax_Syntax.fv_qual = uu____7656;_}
          ->
          let uu____7659 =
            let uu____7664 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7664  in
          (match uu____7659 with
           | (uu____7695,t) ->
               let uu____7697 =
                 let uu____7698 = normalize1 t  in N uu____7698  in
               (uu____7697, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7699;
             FStar_Syntax_Syntax.vars = uu____7700;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7779 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7779 with
           | (unary_op1,uu____7803) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7874;
             FStar_Syntax_Syntax.vars = uu____7875;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7971 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7971 with
           | (unary_op1,uu____7995) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8074;
             FStar_Syntax_Syntax.vars = uu____8075;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8113 = infer env a  in
          (match uu____8113 with
           | (t,s,u) ->
               let uu____8129 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8129 with
                | (head1,uu____8153) ->
                    let uu____8178 =
                      let uu____8179 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8179  in
                    let uu____8180 =
                      let uu____8181 =
                        let uu____8182 =
                          let uu____8199 =
                            let uu____8210 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8210]  in
                          (head1, uu____8199)  in
                        FStar_Syntax_Syntax.Tm_app uu____8182  in
                      mk1 uu____8181  in
                    let uu____8247 =
                      let uu____8248 =
                        let uu____8249 =
                          let uu____8266 =
                            let uu____8277 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8277]  in
                          (head1, uu____8266)  in
                        FStar_Syntax_Syntax.Tm_app uu____8249  in
                      mk1 uu____8248  in
                    (uu____8178, uu____8180, uu____8247)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8314;
             FStar_Syntax_Syntax.vars = uu____8315;_},(a1,uu____8317)::a2::[])
          ->
          let uu____8373 = infer env a1  in
          (match uu____8373 with
           | (t,s,u) ->
               let uu____8389 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8389 with
                | (head1,uu____8413) ->
                    let uu____8438 =
                      let uu____8439 =
                        let uu____8440 =
                          let uu____8457 =
                            let uu____8468 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8468; a2]  in
                          (head1, uu____8457)  in
                        FStar_Syntax_Syntax.Tm_app uu____8440  in
                      mk1 uu____8439  in
                    let uu____8513 =
                      let uu____8514 =
                        let uu____8515 =
                          let uu____8532 =
                            let uu____8543 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8543; a2]  in
                          (head1, uu____8532)  in
                        FStar_Syntax_Syntax.Tm_app uu____8515  in
                      mk1 uu____8514  in
                    (t, uu____8438, uu____8513)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8588;
             FStar_Syntax_Syntax.vars = uu____8589;_},uu____8590)
          ->
          let uu____8615 =
            let uu____8621 =
              let uu____8623 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8623
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8621)  in
          FStar_Errors.raise_error uu____8615 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8633;
             FStar_Syntax_Syntax.vars = uu____8634;_},uu____8635)
          ->
          let uu____8660 =
            let uu____8666 =
              let uu____8668 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8668
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8666)  in
          FStar_Errors.raise_error uu____8660 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8704 = check_n env head1  in
          (match uu____8704 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8727 =
                   let uu____8728 = FStar_Syntax_Subst.compress t  in
                   uu____8728.FStar_Syntax_Syntax.n  in
                 match uu____8727 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8732 -> true
                 | uu____8748 -> false  in
               let rec flatten1 t =
                 let uu____8770 =
                   let uu____8771 = FStar_Syntax_Subst.compress t  in
                   uu____8771.FStar_Syntax_Syntax.n  in
                 match uu____8770 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8790);
                                FStar_Syntax_Syntax.pos = uu____8791;
                                FStar_Syntax_Syntax.vars = uu____8792;_})
                     when is_arrow t1 ->
                     let uu____8821 = flatten1 t1  in
                     (match uu____8821 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8921,uu____8922)
                     -> flatten1 e1
                 | uu____8963 ->
                     let uu____8964 =
                       let uu____8970 =
                         let uu____8972 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____8972
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____8970)  in
                     FStar_Errors.raise_err uu____8964
                  in
               let uu____8990 = flatten1 t_head  in
               (match uu____8990 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9065 =
                          let uu____9071 =
                            let uu____9073 = FStar_Util.string_of_int n1  in
                            let uu____9075 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9077 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9073 uu____9075 uu____9077
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9071)
                           in
                        FStar_Errors.raise_err uu____9065)
                     else ();
                     (let uu____9083 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9083 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9136 args1 =
                            match uu____9136 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9236 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9236
                                 | (binders3,[]) ->
                                     let uu____9274 =
                                       let uu____9275 =
                                         let uu____9278 =
                                           let uu____9279 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9279
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9278
                                          in
                                       uu____9275.FStar_Syntax_Syntax.n  in
                                     (match uu____9274 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9312 =
                                            let uu____9313 =
                                              let uu____9314 =
                                                let uu____9329 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9329)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9314
                                               in
                                            mk1 uu____9313  in
                                          N uu____9312
                                      | uu____9342 -> failwith "wat?")
                                 | ([],uu____9344::uu____9345) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9398)::binders3,(arg,uu____9401)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9488 = FStar_List.splitAt n' binders1  in
                          (match uu____9488 with
                           | (binders2,uu____9522) ->
                               let uu____9555 =
                                 let uu____9578 =
                                   FStar_List.map2
                                     (fun uu____9640  ->
                                        fun uu____9641  ->
                                          match (uu____9640, uu____9641) with
                                          | ((bv,uu____9689),(arg,q)) ->
                                              let uu____9718 =
                                                let uu____9719 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9719.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9718 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9740 ->
                                                   let uu____9741 =
                                                     let uu____9748 =
                                                       star_type' env arg  in
                                                     (uu____9748, q)  in
                                                   (uu____9741, [(arg, q)])
                                               | uu____9785 ->
                                                   let uu____9786 =
                                                     check_n env arg  in
                                                   (match uu____9786 with
                                                    | (uu____9811,s_arg,u_arg)
                                                        ->
                                                        let uu____9814 =
                                                          let uu____9823 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9823
                                                          then
                                                            let uu____9834 =
                                                              let uu____9841
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9841, q)
                                                               in
                                                            [uu____9834;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9814))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9578  in
                               (match uu____9555 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____9969 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____9982 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____9969, uu____9982)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10051) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10057) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10063,uu____10064) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10106 =
            let uu____10107 = env.tc_const c  in N uu____10107  in
          (uu____10106, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10114 ->
          let uu____10128 =
            let uu____10130 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10130  in
          failwith uu____10128
      | FStar_Syntax_Syntax.Tm_type uu____10139 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10147 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10169 ->
          let uu____10176 =
            let uu____10178 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10178  in
          failwith uu____10176
      | FStar_Syntax_Syntax.Tm_uvar uu____10187 ->
          let uu____10200 =
            let uu____10202 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10202  in
          failwith uu____10200
      | FStar_Syntax_Syntax.Tm_delayed uu____10211 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10241 =
            let uu____10243 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10243  in
          failwith uu____10241

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
          let uu____10292 = check_n env e0  in
          match uu____10292 with
          | (uu____10305,s_e0,u_e0) ->
              let uu____10308 =
                let uu____10337 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10398 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10398 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1114_10440 = env  in
                             let uu____10441 =
                               let uu____10442 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10442
                                in
                             {
                               tcenv = uu____10441;
                               subst = (uu___1114_10440.subst);
                               tc_const = (uu___1114_10440.tc_const)
                             }  in
                           let uu____10445 = f env1 body  in
                           (match uu____10445 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10517 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10337  in
              (match uu____10308 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10623 = FStar_List.hd nms  in
                     match uu____10623 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10632  ->
                          match uu___10_10632 with
                          | M uu____10634 -> true
                          | uu____10636 -> false) nms
                      in
                   let uu____10638 =
                     let uu____10675 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10765  ->
                              match uu____10765 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____10949 =
                                         check env original_body (M t2)  in
                                       (match uu____10949 with
                                        | (uu____10986,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11025,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10675  in
                   (match uu____10638 with
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
                              (fun uu____11214  ->
                                 match uu____11214 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11265 =
                                         let uu____11266 =
                                           let uu____11283 =
                                             let uu____11294 =
                                               let uu____11303 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11306 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11303, uu____11306)  in
                                             [uu____11294]  in
                                           (s_body, uu____11283)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11266
                                          in
                                       mk1 uu____11265  in
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
                            let uu____11441 =
                              let uu____11442 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11442]  in
                            let uu____11461 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11441 uu____11461
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11485 =
                              let uu____11494 =
                                let uu____11501 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11501
                                 in
                              [uu____11494]  in
                            let uu____11520 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11485 uu____11520
                             in
                          let uu____11523 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11562 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11523, uu____11562)
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
                           let uu____11672 =
                             let uu____11673 =
                               let uu____11674 =
                                 let uu____11701 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11701,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11674
                                in
                             mk1 uu____11673  in
                           let uu____11760 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11672, uu____11760))))

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
              let uu____11825 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11825]  in
            let uu____11844 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11844 with
            | (x_binders1,e21) ->
                let uu____11857 = infer env e1  in
                (match uu____11857 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____11874 = is_C t1  in
                       if uu____11874
                       then
                         let uu___1200_11877 = binding  in
                         let uu____11878 =
                           let uu____11881 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____11881  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1200_11877.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1200_11877.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11878;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1200_11877.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1200_11877.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1200_11877.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1200_11877.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1203_11885 = env  in
                       let uu____11886 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1205_11888 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1205_11888.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1205_11888.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11886;
                         subst = (uu___1203_11885.subst);
                         tc_const = (uu___1203_11885.tc_const)
                       }  in
                     let uu____11889 = proceed env1 e21  in
                     (match uu____11889 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1212_11906 = binding  in
                            let uu____11907 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1212_11906.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1212_11906.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11907;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1212_11906.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1212_11906.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1212_11906.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1212_11906.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____11910 =
                            let uu____11911 =
                              let uu____11912 =
                                let uu____11926 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1215_11943 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1215_11943.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1215_11943.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1215_11943.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1215_11943.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1215_11943.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1215_11943.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11926)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11912  in
                            mk1 uu____11911  in
                          let uu____11944 =
                            let uu____11945 =
                              let uu____11946 =
                                let uu____11960 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1217_11977 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1217_11977.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1217_11977.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1217_11977.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1217_11977.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1217_11977.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1217_11977.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11960)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11946  in
                            mk1 uu____11945  in
                          (nm_rec, uu____11910, uu____11944))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1224_11982 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1224_11982.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1224_11982.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1224_11982.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1224_11982.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1224_11982.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1227_11984 = env  in
                       let uu____11985 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1229_11987 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1229_11987.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1229_11987.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11985;
                         subst = (uu___1227_11984.subst);
                         tc_const = (uu___1227_11984.tc_const)
                       }  in
                     let uu____11988 = ensure_m env1 e21  in
                     (match uu____11988 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12012 =
                              let uu____12013 =
                                let uu____12030 =
                                  let uu____12041 =
                                    let uu____12050 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12053 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12050, uu____12053)  in
                                  [uu____12041]  in
                                (s_e2, uu____12030)  in
                              FStar_Syntax_Syntax.Tm_app uu____12013  in
                            mk1 uu____12012  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12095 =
                              let uu____12096 =
                                let uu____12113 =
                                  let uu____12124 =
                                    let uu____12133 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12133)  in
                                  [uu____12124]  in
                                (s_e1, uu____12113)  in
                              FStar_Syntax_Syntax.Tm_app uu____12096  in
                            mk1 uu____12095  in
                          let uu____12169 =
                            let uu____12170 =
                              let uu____12171 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12171]  in
                            FStar_Syntax_Util.abs uu____12170 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12190 =
                            let uu____12191 =
                              let uu____12192 =
                                let uu____12206 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1241_12223 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1241_12223.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1241_12223.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1241_12223.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1241_12223.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1241_12223.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1241_12223.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12206)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12192  in
                            mk1 uu____12191  in
                          ((M t2), uu____12169, uu____12190)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12233 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12233  in
      let uu____12234 = check env e mn  in
      match uu____12234 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12250 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12273 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12273  in
      let uu____12274 = check env e mn  in
      match uu____12274 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12290 -> failwith "[check_m]: impossible"

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
        (let uu____12323 =
           let uu____12325 = is_C c  in Prims.op_Negation uu____12325  in
         if uu____12323 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12339 =
           let uu____12340 = FStar_Syntax_Subst.compress c  in
           uu____12340.FStar_Syntax_Syntax.n  in
         match uu____12339 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12369 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12369 with
              | (wp_head,wp_args) ->
                  ((let uu____12413 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12432 =
                           let uu____12434 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12434
                            in
                         Prims.op_Negation uu____12432)
                       in
                    if uu____12413 then failwith "mismatch" else ());
                   (let uu____12447 =
                      let uu____12448 =
                        let uu____12465 =
                          FStar_List.map2
                            (fun uu____12503  ->
                               fun uu____12504  ->
                                 match (uu____12503, uu____12504) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12566 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12566
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12575 =
                                         let uu____12577 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12577 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12575
                                       then
                                         let uu____12579 =
                                           let uu____12585 =
                                             let uu____12587 =
                                               print_implicit q  in
                                             let uu____12589 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12587 uu____12589
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12585)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12579
                                       else ());
                                      (let uu____12595 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12595, q)))) args wp_args
                           in
                        (head1, uu____12465)  in
                      FStar_Syntax_Syntax.Tm_app uu____12448  in
                    mk1 uu____12447)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12641 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12641 with
              | (binders_orig,comp1) ->
                  let uu____12648 =
                    let uu____12665 =
                      FStar_List.map
                        (fun uu____12705  ->
                           match uu____12705 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12733 = is_C h  in
                               if uu____12733
                               then
                                 let w' =
                                   let uu____12749 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12749
                                    in
                                 let uu____12751 =
                                   let uu____12760 =
                                     let uu____12769 =
                                       let uu____12776 =
                                         let uu____12777 =
                                           let uu____12778 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12778  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12777
                                          in
                                       (uu____12776, q)  in
                                     [uu____12769]  in
                                   (w', q) :: uu____12760  in
                                 (w', uu____12751)
                               else
                                 (let x =
                                    let uu____12812 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____12812
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12665  in
                  (match uu____12648 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____12886 =
                           let uu____12889 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12889
                            in
                         FStar_Syntax_Subst.subst_comp uu____12886 comp1  in
                       let app =
                         let uu____12893 =
                           let uu____12894 =
                             let uu____12911 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____12930 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____12931 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12930, uu____12931)) bvs
                                in
                             (wp, uu____12911)  in
                           FStar_Syntax_Syntax.Tm_app uu____12894  in
                         mk1 uu____12893  in
                       let comp3 =
                         let uu____12946 = type_of_comp comp2  in
                         let uu____12947 = is_monadic_comp comp2  in
                         trans_G env uu____12946 uu____12947 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____12950,uu____12951) ->
             trans_F_ env e wp
         | uu____12992 -> failwith "impossible trans_F_")

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
            let uu____13000 =
              let uu____13001 = star_type' env h  in
              let uu____13004 =
                let uu____13015 =
                  let uu____13024 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13024)  in
                [uu____13015]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13001;
                FStar_Syntax_Syntax.effect_args = uu____13004;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13000
          else
            (let uu____13050 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13050)

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
    fun t  -> let uu____13071 = n env.tcenv t  in star_type' env uu____13071
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13091 = n env.tcenv t  in check_n env uu____13091
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13108 = n env.tcenv c  in
        let uu____13109 = n env.tcenv wp  in
        trans_F_ env uu____13108 uu____13109
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____13129 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13129
         then
           let uu____13133 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s
             uu____13133
         else ());
        (let uu____13138 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____13138 with
         | (t',uu____13146,uu____13147) ->
             ((let uu____13149 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____13149
               then
                 let uu____13153 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____13153
               else ());
              t'))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun ed  ->
      let uu____13189 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature)
         in
      match uu____13189 with
      | (effect_binders_un,signature_un) ->
          let uu____13210 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____13210 with
           | (effect_binders,env1,uu____13229) ->
               let uu____13230 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____13230 with
                | (signature,uu____13246) ->
                    let raise_error1 uu____13262 =
                      match uu____13262 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____13298  ->
                           match uu____13298 with
                           | (bv,qual) ->
                               let uu____13317 =
                                 let uu___1367_13318 = bv  in
                                 let uu____13319 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1367_13318.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1367_13318.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____13319
                                 }  in
                               (uu____13317, qual)) effect_binders
                       in
                    let uu____13324 =
                      let uu____13331 =
                        let uu____13332 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____13332.FStar_Syntax_Syntax.n  in
                      match uu____13331 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____13342)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____13374 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____13324 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____13400 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____13400
                           then
                             let uu____13403 =
                               let uu____13406 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____13406  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____13403
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____13454 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____13454 with
                           | (t2,comp,uu____13467) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____13476 =
                           let uu____13481 =
                             let uu____13482 =
                               let uu____13491 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____13491
                                 FStar_Util.must
                                in
                             FStar_All.pipe_right uu____13482
                               FStar_Pervasives_Native.snd
                              in
                           open_and_check env1 [] uu____13481  in
                         (match uu____13476 with
                          | (repr,_comp) ->
                              ((let uu____13537 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____13537
                                then
                                  let uu____13541 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____13541
                                else ());
                               (let dmff_env =
                                  empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange)
                                   in
                                let wp_type = star_type dmff_env repr  in
                                let uu____13548 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____13551 =
                                    let uu____13552 =
                                      let uu____13553 =
                                        let uu____13570 =
                                          let uu____13581 =
                                            let uu____13590 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____13593 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____13590, uu____13593)  in
                                          [uu____13581]  in
                                        (wp_type, uu____13570)  in
                                      FStar_Syntax_Syntax.Tm_app uu____13553
                                       in
                                    mk1 uu____13552  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____13551
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____13641 =
                                      let uu____13648 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____13648)  in
                                    let uu____13654 =
                                      let uu____13663 =
                                        let uu____13670 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____13670
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____13663]  in
                                    uu____13641 :: uu____13654  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____13707 =
                                  recheck_debug
                                    "turned into the effect signature" env1
                                    effect_signature
                                   in
                                let sigelts = FStar_Util.mk_ref []  in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name  in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env2 = get_env dmff_env1  in
                                  let uu____13773 = item  in
                                  match uu____13773 with
                                  | (u_item,item1) ->
                                      let uu____13788 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____13788 with
                                       | (item2,item_comp) ->
                                           ((let uu____13804 =
                                               let uu____13806 =
                                                 FStar_TypeChecker_Common.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____13806
                                                in
                                             if uu____13804
                                             then
                                               let uu____13809 =
                                                 let uu____13815 =
                                                   let uu____13817 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____13819 =
                                                     FStar_TypeChecker_Common.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____13817 uu____13819
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____13815)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____13809
                                             else ());
                                            (let uu____13825 =
                                               star_expr dmff_env1 item2  in
                                             match uu____13825 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____13843 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____13845 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____13847 =
                                  let uu____13856 =
                                    let uu____13861 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____13861
                                      FStar_Util.must
                                     in
                                  elaborate_and_star dmff_env [] uu____13856
                                   in
                                match uu____13847 with
                                | (dmff_env1,uu____13889,bind_wp,bind_elab)
                                    ->
                                    let uu____13892 =
                                      let uu____13901 =
                                        let uu____13906 =
                                          FStar_All.pipe_right ed
                                            FStar_Syntax_Util.get_return_repr
                                           in
                                        FStar_All.pipe_right uu____13906
                                          FStar_Util.must
                                         in
                                      elaborate_and_star dmff_env1 []
                                        uu____13901
                                       in
                                    (match uu____13892 with
                                     | (dmff_env2,uu____13950,return_wp,return_elab)
                                         ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           }  in
                                         let lift_from_pure_wp =
                                           let uu____13959 =
                                             let uu____13960 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____13960.FStar_Syntax_Syntax.n
                                              in
                                           match uu____13959 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____14018 =
                                                 let uu____14037 =
                                                   let uu____14042 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____14042
                                                    in
                                                 match uu____14037 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____14124 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____14018 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____14178 =
                                                        get_env dmff_env2  in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____14178
                                                        [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____14201 =
                                                          let uu____14202 =
                                                            let uu____14219 =
                                                              let uu____14230
                                                                =
                                                                let uu____14239
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____14244
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____14239,
                                                                  uu____14244)
                                                                 in
                                                              [uu____14230]
                                                               in
                                                            (wp_type,
                                                              uu____14219)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____14202
                                                           in
                                                        mk1 uu____14201  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____14280 =
                                                      let uu____14289 =
                                                        let uu____14290 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____14290
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____14289
                                                       in
                                                    (match uu____14280 with
                                                     | (bs1,body2,what') ->
                                                         let fail1
                                                           uu____14313 =
                                                           let error_msg =
                                                             let uu____14316
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____14318
                                                               =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.text_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____14316
                                                               uu____14318
                                                              in
                                                           raise_error1
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg)
                                                            in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail1 ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____14328
                                                                   =
                                                                   let uu____14330
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____14330
                                                                    in
                                                                 if
                                                                   uu____14328
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____14335
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env1
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0
                                                                     in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail1 ())
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____14335
                                                                   (fun a1 
                                                                    -> ()))));
                                                          (let wp =
                                                             let t2 =
                                                               (FStar_Pervasives_Native.fst
                                                                  b21).FStar_Syntax_Syntax.sort
                                                                in
                                                             let pure_wp_type
                                                               =
                                                               double_star t2
                                                                in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type
                                                              in
                                                           let body3 =
                                                             let uu____14364
                                                               =
                                                               let uu____14369
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____14370
                                                                 =
                                                                 let uu____14371
                                                                   =
                                                                   let uu____14380
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____14380,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____14371]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____14369
                                                                 uu____14370
                                                                in
                                                             uu____14364
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____14415 =
                                                             let uu____14416
                                                               =
                                                               let uu____14425
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____14425]
                                                                in
                                                             b11 ::
                                                               uu____14416
                                                              in
                                                           let uu____14450 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____14415
                                                             uu____14450
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____14453 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____14461 =
                                             let uu____14462 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____14462.FStar_Syntax_Syntax.n
                                              in
                                           match uu____14461 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____14520 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____14520
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____14541 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____14549 =
                                             let uu____14550 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____14550.FStar_Syntax_Syntax.n
                                              in
                                           match uu____14549 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____14584 =
                                                 let uu____14585 =
                                                   let uu____14594 =
                                                     let uu____14601 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____14601
                                                      in
                                                   [uu____14594]  in
                                                 FStar_List.append
                                                   uu____14585 binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____14584 body what
                                           | uu____14620 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind")
                                            in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = Prims.int_zero
                                           then t
                                           else
                                             (let uu____14650 =
                                                let uu____14651 =
                                                  let uu____14652 =
                                                    let uu____14669 =
                                                      let uu____14680 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____14680
                                                       in
                                                    (t, uu____14669)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____14652
                                                   in
                                                mk1 uu____14651  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____14650)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] -> failwith "empty path.."
                                           | a2::[] ->
                                               let uu____14738 = f a2  in
                                               [uu____14738]
                                           | x::xs ->
                                               let uu____14749 =
                                                 apply_last1 f xs  in
                                               x :: uu____14749
                                            in
                                         let register name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname
                                              in
                                           let p' =
                                             apply_last1
                                               (fun s  ->
                                                  Prims.op_Hat "__"
                                                    (Prims.op_Hat s
                                                       (Prims.op_Hat
                                                          "_eff_override_"
                                                          name))) p
                                              in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               FStar_Range.dummyRange
                                              in
                                           let uu____14783 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____14783 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____14813 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____14813
                                                 then
                                                   let uu____14816 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____14816
                                                 else ());
                                                (let uu____14821 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____14821))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____14830 =
                                                 let uu____14835 =
                                                   mk_lid name  in
                                                 let uu____14836 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____14835
                                                   uu____14836
                                                  in
                                               (match uu____14830 with
                                                | (sigelt,fv) ->
                                                    ((let uu____14840 =
                                                        let uu____14843 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____14843
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____14840);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____14897 =
                                             let uu____14900 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____14903 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____14900 :: uu____14903  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____14897);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____14955 =
                                              let uu____14958 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____14959 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____14958 :: uu____14959  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____14955);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____15011 =
                                               let uu____15014 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____15017 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____15014 :: uu____15017  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____15011);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____15069 =
                                                let uu____15072 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____15073 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____15072 :: uu____15073
                                                 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____15069);
                                             (let uu____15122 =
                                                FStar_List.fold_left
                                                  (fun uu____15162  ->
                                                     fun action  ->
                                                       match uu____15162 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____15183 =
                                                             let uu____15190
                                                               =
                                                               get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____15190
                                                               params_un
                                                              in
                                                           (match uu____15183
                                                            with
                                                            | (action_params,env',uu____15199)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____15225
                                                                     ->
                                                                    match uu____15225
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____15244
                                                                    =
                                                                    let uu___1560_15245
                                                                    = bv  in
                                                                    let uu____15246
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___1560_15245.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1560_15245.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____15246
                                                                    }  in
                                                                    (uu____15244,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____15252
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____15252
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    ((action.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
                                                                     in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp
                                                                     in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1
                                                                     in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab
                                                                     in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp
                                                                     in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____15291
                                                                    ->
                                                                    let uu____15292
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____15292
                                                                     in
                                                                    ((
                                                                    let uu____15296
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____15296
                                                                    then
                                                                    let uu____15301
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____15304
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____15307
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____15309
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____15301
                                                                    uu____15304
                                                                    uu____15307
                                                                    uu____15309
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2
                                                                     in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____15318
                                                                    =
                                                                    let uu____15321
                                                                    =
                                                                    let uu___1582_15322
                                                                    = action
                                                                     in
                                                                    let uu____15323
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____15324
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1582_15322.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1582_15322.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___1582_15322.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____15323;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____15324
                                                                    }  in
                                                                    uu____15321
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____15318))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____15122 with
                                              | (dmff_env3,actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions
                                                     in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a
                                                       in
                                                    let binders =
                                                      let uu____15368 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____15375 =
                                                        let uu____15384 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____15384]  in
                                                      uu____15368 ::
                                                        uu____15375
                                                       in
                                                    let uu____15409 =
                                                      let uu____15412 =
                                                        let uu____15413 =
                                                          let uu____15414 =
                                                            let uu____15431 =
                                                              let uu____15442
                                                                =
                                                                let uu____15451
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____15454
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____15451,
                                                                  uu____15454)
                                                                 in
                                                              [uu____15442]
                                                               in
                                                            (repr,
                                                              uu____15431)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____15414
                                                           in
                                                        mk1 uu____15413  in
                                                      let uu____15490 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      trans_F dmff_env3
                                                        uu____15412
                                                        uu____15490
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____15409
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____15491 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____15495 =
                                                    let uu____15504 =
                                                      let uu____15505 =
                                                        let uu____15508 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____15508
                                                         in
                                                      uu____15505.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____15504 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____15522)
                                                        ->
                                                        let uu____15559 =
                                                          let uu____15580 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____15580
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____15648 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____15559
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____15713
                                                               =
                                                               let uu____15714
                                                                 =
                                                                 let uu____15717
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____15717
                                                                  in
                                                               uu____15714.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____15713
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____15750
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____15750
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____15765
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____15796
                                                                     ->
                                                                    match uu____15796
                                                                    with
                                                                    | 
                                                                    (bv,uu____15805)
                                                                    ->
                                                                    let uu____15810
                                                                    =
                                                                    let uu____15812
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15812
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15810
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____15765
                                                                    with
                                                                    | 
                                                                    (pre_args,post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post::[]
                                                                    -> post
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____15904
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____15904
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____15914
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____15925
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____15925
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____15935
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____15938
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____15935,
                                                                    uu____15938)))
                                                              | uu____15953
                                                                  ->
                                                                  let uu____15954
                                                                    =
                                                                    let uu____15960
                                                                    =
                                                                    let uu____15962
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____15962
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____15960)
                                                                     in
                                                                  raise_error1
                                                                    uu____15954))
                                                    | uu____15974 ->
                                                        let uu____15975 =
                                                          let uu____15981 =
                                                            let uu____15983 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____15983
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____15981)
                                                           in
                                                        raise_error1
                                                          uu____15975
                                                     in
                                                  (match uu____15495 with
                                                   | (pre,post) ->
                                                       ((let uu____16016 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____16019 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____16022 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed_combs =
                                                           match ed.FStar_Syntax_Syntax.combinators
                                                           with
                                                           | FStar_Syntax_Syntax.DM4F_eff
                                                               combs ->
                                                               let uu____16026
                                                                 =
                                                                 let uu___1640_16027
                                                                   = combs
                                                                    in
                                                                 let uu____16028
                                                                   =
                                                                   let uu____16029
                                                                    =
                                                                    apply_close
                                                                    return_wp2
                                                                     in
                                                                   ([],
                                                                    uu____16029)
                                                                    in
                                                                 let uu____16036
                                                                   =
                                                                   let uu____16037
                                                                    =
                                                                    apply_close
                                                                    bind_wp2
                                                                     in
                                                                   ([],
                                                                    uu____16037)
                                                                    in
                                                                 let uu____16044
                                                                   =
                                                                   let uu____16047
                                                                    =
                                                                    let uu____16048
                                                                    =
                                                                    apply_close
                                                                    repr2  in
                                                                    ([],
                                                                    uu____16048)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16047
                                                                    in
                                                                 let uu____16055
                                                                   =
                                                                   let uu____16058
                                                                    =
                                                                    let uu____16059
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                    ([],
                                                                    uu____16059)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16058
                                                                    in
                                                                 let uu____16066
                                                                   =
                                                                   let uu____16069
                                                                    =
                                                                    let uu____16070
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    ([],
                                                                    uu____16070)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16069
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.ret_wp
                                                                    =
                                                                    uu____16028;
                                                                   FStar_Syntax_Syntax.bind_wp
                                                                    =
                                                                    uu____16036;
                                                                   FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    (uu___1640_16027.FStar_Syntax_Syntax.stronger);
                                                                   FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    (uu___1640_16027.FStar_Syntax_Syntax.if_then_else);
                                                                   FStar_Syntax_Syntax.ite_wp
                                                                    =
                                                                    (uu___1640_16027.FStar_Syntax_Syntax.ite_wp);
                                                                   FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    (uu___1640_16027.FStar_Syntax_Syntax.close_wp);
                                                                   FStar_Syntax_Syntax.trivial
                                                                    =
                                                                    (uu___1640_16027.FStar_Syntax_Syntax.trivial);
                                                                   FStar_Syntax_Syntax.repr
                                                                    =
                                                                    uu____16044;
                                                                   FStar_Syntax_Syntax.return_repr
                                                                    =
                                                                    uu____16055;
                                                                   FStar_Syntax_Syntax.bind_repr
                                                                    =
                                                                    uu____16066
                                                                 }  in
                                                               FStar_Syntax_Syntax.DM4F_eff
                                                                 uu____16026
                                                           | uu____16077 ->
                                                               failwith
                                                                 "Impossible! For a DM4F effect combinators must be in DM4f_eff"
                                                            in
                                                         let ed1 =
                                                           let uu___1644_16080
                                                             = ed  in
                                                           let uu____16081 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____16082 =
                                                             let uu____16083
                                                               =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature
                                                                in
                                                             ([],
                                                               uu____16083)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___1644_16080.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___1644_16080.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___1644_16080.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____16081;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____16082;
                                                             FStar_Syntax_Syntax.combinators
                                                               = ed_combs;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___1644_16080.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____16090 =
                                                           gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____16090
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____16108
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____16108
                                                               then
                                                                 let uu____16112
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____16112
                                                               else ());
                                                              (let lift_from_pure_opt
                                                                 =
                                                                 if
                                                                   (FStar_List.length
                                                                    effect_binders1)
                                                                    =
                                                                    Prims.int_zero
                                                                 then
                                                                   let lift_from_pure
                                                                    =
                                                                    let uu____16132
                                                                    =
                                                                    let uu____16135
                                                                    =
                                                                    let uu____16136
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____16136)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16135
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____16132;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____16143
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16143
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____16146
                                                                 =
                                                                 let uu____16149
                                                                   =
                                                                   let uu____16152
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____16152
                                                                    in
                                                                 FStar_List.append
                                                                   uu____16149
                                                                   sigelts'
                                                                  in
                                                               (uu____16146,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  