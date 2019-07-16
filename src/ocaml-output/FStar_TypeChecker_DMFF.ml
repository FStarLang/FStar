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
                    if (FStar_List.length binders) > (Prims.parse_int "0")
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
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
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
                      let uu____1916 =
                        let uu____1927 =
                          let uu____1930 =
                            let uu____1931 =
                              let uu____1942 =
                                let uu____1945 =
                                  let uu____1946 =
                                    let uu____1957 =
                                      let uu____1966 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1966
                                       in
                                    [uu____1957]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1946
                                   in
                                [uu____1945]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1942
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1931  in
                          let uu____1991 =
                            let uu____1994 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1994]  in
                          uu____1930 :: uu____1991  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1927
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1916  in
                    let uu____2003 =
                      let uu____2004 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2004  in
                    FStar_Syntax_Util.abs uu____2003 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2020 = mk_lid "wp_assume"  in
                    register env1 uu____2020 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2033 =
                        let uu____2042 =
                          let uu____2049 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2049  in
                        [uu____2042]  in
                      let uu____2062 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2033 uu____2062  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2070 =
                        let uu____2081 =
                          let uu____2084 =
                            let uu____2085 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2085  in
                          let uu____2104 =
                            let uu____2107 =
                              let uu____2108 =
                                let uu____2119 =
                                  let uu____2122 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2122]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2119
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2108  in
                            [uu____2107]  in
                          uu____2084 :: uu____2104  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2081
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2070  in
                    let uu____2139 =
                      let uu____2140 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2140  in
                    FStar_Syntax_Util.abs uu____2139 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2156 = mk_lid "wp_close"  in
                    register env1 uu____2156 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2167 =
                      let uu____2168 =
                        let uu____2169 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2169
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2168  in
                    FStar_Pervasives_Native.Some uu____2167  in
                  let mk_forall1 x body =
                    let uu____2181 =
                      let uu____2188 =
                        let uu____2189 =
                          let uu____2206 =
                            let uu____2217 =
                              let uu____2226 =
                                let uu____2227 =
                                  let uu____2228 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2228]  in
                                FStar_Syntax_Util.abs uu____2227 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2226  in
                            [uu____2217]  in
                          (FStar_Syntax_Util.tforall, uu____2206)  in
                        FStar_Syntax_Syntax.Tm_app uu____2189  in
                      FStar_Syntax_Syntax.mk uu____2188  in
                    uu____2181 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2286 =
                      let uu____2287 = FStar_Syntax_Subst.compress t  in
                      uu____2287.FStar_Syntax_Syntax.n  in
                    match uu____2286 with
                    | FStar_Syntax_Syntax.Tm_type uu____2291 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2324  ->
                              match uu____2324 with
                              | (b,uu____2333) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2338 -> true  in
                  let rec is_monotonic t =
                    let uu____2351 =
                      let uu____2352 = FStar_Syntax_Subst.compress t  in
                      uu____2352.FStar_Syntax_Syntax.n  in
                    match uu____2351 with
                    | FStar_Syntax_Syntax.Tm_type uu____2356 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2389  ->
                              match uu____2389 with
                              | (b,uu____2398) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2403 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2477 =
                      let uu____2478 = FStar_Syntax_Subst.compress t1  in
                      uu____2478.FStar_Syntax_Syntax.n  in
                    match uu____2477 with
                    | FStar_Syntax_Syntax.Tm_type uu____2483 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2486);
                                      FStar_Syntax_Syntax.pos = uu____2487;
                                      FStar_Syntax_Syntax.vars = uu____2488;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2532 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2532
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2542 =
                              let uu____2545 =
                                let uu____2556 =
                                  let uu____2565 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2565  in
                                [uu____2556]  in
                              FStar_Syntax_Util.mk_app x uu____2545  in
                            let uu____2582 =
                              let uu____2585 =
                                let uu____2596 =
                                  let uu____2605 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2605  in
                                [uu____2596]  in
                              FStar_Syntax_Util.mk_app y uu____2585  in
                            mk_rel1 b uu____2542 uu____2582  in
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
                             let uu____2629 =
                               let uu____2632 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2635 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2632 uu____2635  in
                             let uu____2638 =
                               let uu____2641 =
                                 let uu____2644 =
                                   let uu____2655 =
                                     let uu____2664 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2664
                                      in
                                   [uu____2655]  in
                                 FStar_Syntax_Util.mk_app x uu____2644  in
                               let uu____2681 =
                                 let uu____2684 =
                                   let uu____2695 =
                                     let uu____2704 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2704
                                      in
                                   [uu____2695]  in
                                 FStar_Syntax_Util.mk_app y uu____2684  in
                               mk_rel1 b uu____2641 uu____2681  in
                             FStar_Syntax_Util.mk_imp uu____2629 uu____2638
                              in
                           let uu____2721 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2721)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2724);
                                      FStar_Syntax_Syntax.pos = uu____2725;
                                      FStar_Syntax_Syntax.vars = uu____2726;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2770 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2770
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2780 =
                              let uu____2783 =
                                let uu____2794 =
                                  let uu____2803 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2803  in
                                [uu____2794]  in
                              FStar_Syntax_Util.mk_app x uu____2783  in
                            let uu____2820 =
                              let uu____2823 =
                                let uu____2834 =
                                  let uu____2843 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2843  in
                                [uu____2834]  in
                              FStar_Syntax_Util.mk_app y uu____2823  in
                            mk_rel1 b uu____2780 uu____2820  in
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
                             let uu____2867 =
                               let uu____2870 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2873 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2870 uu____2873  in
                             let uu____2876 =
                               let uu____2879 =
                                 let uu____2882 =
                                   let uu____2893 =
                                     let uu____2902 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2902
                                      in
                                   [uu____2893]  in
                                 FStar_Syntax_Util.mk_app x uu____2882  in
                               let uu____2919 =
                                 let uu____2922 =
                                   let uu____2933 =
                                     let uu____2942 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2942
                                      in
                                   [uu____2933]  in
                                 FStar_Syntax_Util.mk_app y uu____2922  in
                               mk_rel1 b uu____2879 uu____2919  in
                             FStar_Syntax_Util.mk_imp uu____2867 uu____2876
                              in
                           let uu____2959 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2959)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___235_2998 = t1  in
                          let uu____2999 =
                            let uu____3000 =
                              let uu____3015 =
                                let uu____3018 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3018  in
                              ([binder], uu____3015)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3000  in
                          {
                            FStar_Syntax_Syntax.n = uu____2999;
                            FStar_Syntax_Syntax.pos =
                              (uu___235_2998.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___235_2998.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3041 ->
                        failwith "unhandled arrow"
                    | uu____3059 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____3096 =
                        let uu____3097 = FStar_Syntax_Subst.compress t1  in
                        uu____3097.FStar_Syntax_Syntax.n  in
                      match uu____3096 with
                      | FStar_Syntax_Syntax.Tm_type uu____3100 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3127 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3127
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3148 =
                                let uu____3149 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3149 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3148
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3179 =
                            let uu____3190 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3208  ->
                                     match uu____3208 with
                                     | (t2,q) ->
                                         let uu____3228 = project i x  in
                                         let uu____3231 = project i y  in
                                         mk_stronger t2 uu____3228 uu____3231)
                                args
                               in
                            match uu____3190 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3179 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3285);
                                      FStar_Syntax_Syntax.pos = uu____3286;
                                      FStar_Syntax_Syntax.vars = uu____3287;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3331  ->
                                   match uu____3331 with
                                   | (bv,q) ->
                                       let uu____3345 =
                                         let uu____3347 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3347  in
                                       FStar_Syntax_Syntax.gen_bv uu____3345
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3356 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3356) bvs
                             in
                          let body =
                            let uu____3358 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3361 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3358 uu____3361  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3370);
                                      FStar_Syntax_Syntax.pos = uu____3371;
                                      FStar_Syntax_Syntax.vars = uu____3372;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3416  ->
                                   match uu____3416 with
                                   | (bv,q) ->
                                       let uu____3430 =
                                         let uu____3432 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3432  in
                                       FStar_Syntax_Syntax.gen_bv uu____3430
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3441 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3441) bvs
                             in
                          let body =
                            let uu____3443 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3446 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3443 uu____3446  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3453 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3456 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3459 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3462 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3456 uu____3459 uu____3462  in
                    let uu____3465 =
                      let uu____3466 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3466  in
                    FStar_Syntax_Util.abs uu____3465 body ret_tot_type  in
                  let stronger1 =
                    let uu____3508 = mk_lid "stronger"  in
                    register env1 uu____3508 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3516 = FStar_Util.prefix gamma  in
                    match uu____3516 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3582 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3582
                             in
                          let uu____3587 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3587 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3597 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3597  in
                              let guard_free1 =
                                let uu____3609 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3609  in
                              let pat =
                                let uu____3613 =
                                  let uu____3624 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3624]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3613
                                 in
                              let pattern_guarded_body =
                                let uu____3652 =
                                  let uu____3653 =
                                    let uu____3660 =
                                      let uu____3661 =
                                        let uu____3682 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1
                                           in
                                        let uu____3687 =
                                          let uu____3700 =
                                            let uu____3711 =
                                              FStar_Syntax_Syntax.as_arg pat
                                               in
                                            [uu____3711]  in
                                          [uu____3700]  in
                                        (uu____3682, uu____3687)  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3661
                                       in
                                    (body, uu____3660)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3653  in
                                mk1 uu____3652  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3774 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3783 =
                            let uu____3786 =
                              let uu____3787 =
                                let uu____3790 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3793 =
                                  let uu____3804 = args_of_binders1 wp_args
                                     in
                                  let uu____3807 =
                                    let uu____3810 =
                                      let uu____3811 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3811
                                       in
                                    [uu____3810]  in
                                  FStar_List.append uu____3804 uu____3807  in
                                FStar_Syntax_Util.mk_app uu____3790
                                  uu____3793
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3787  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3786
                             in
                          FStar_Syntax_Util.abs gamma uu____3783
                            ret_gtot_type
                           in
                        let uu____3812 =
                          let uu____3813 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3813  in
                        FStar_Syntax_Util.abs uu____3812 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3829 = mk_lid "ite_wp"  in
                    register env1 uu____3829 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3837 = FStar_Util.prefix gamma  in
                    match uu____3837 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3895 =
                            let uu____3896 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3903 =
                              let uu____3914 =
                                let uu____3923 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3923  in
                              [uu____3914]  in
                            FStar_Syntax_Util.mk_app uu____3896 uu____3903
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3895
                           in
                        let uu____3940 =
                          let uu____3941 =
                            let uu____3950 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3950 gamma  in
                          FStar_List.append binders uu____3941  in
                        FStar_Syntax_Util.abs uu____3940 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3972 = mk_lid "null_wp"  in
                    register env1 uu____3972 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3985 =
                        let uu____3996 =
                          let uu____3999 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4000 =
                            let uu____4003 =
                              let uu____4004 =
                                let uu____4015 =
                                  let uu____4024 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4024  in
                                [uu____4015]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4004
                               in
                            let uu____4041 =
                              let uu____4044 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4044]  in
                            uu____4003 :: uu____4041  in
                          uu____3999 :: uu____4000  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3996
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3985  in
                    let uu____4053 =
                      let uu____4054 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4054  in
                    FStar_Syntax_Util.abs uu____4053 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4070 = mk_lid "wp_trivial"  in
                    register env1 uu____4070 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4076 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4076
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4088 =
                      let uu____4089 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4089  in
                    let uu____4115 =
                      let uu___342_4116 = ed  in
                      let uu____4117 =
                        let uu____4118 = c wp_if_then_else2  in
                        ([], uu____4118)  in
                      let uu____4125 =
                        let uu____4126 = c ite_wp2  in ([], uu____4126)  in
                      let uu____4133 =
                        let uu____4134 = c stronger2  in ([], uu____4134)  in
                      let uu____4141 =
                        let uu____4142 = c wp_close2  in ([], uu____4142)  in
                      let uu____4149 =
                        let uu____4150 = c wp_assume2  in ([], uu____4150)
                         in
                      let uu____4157 =
                        let uu____4158 = c null_wp2  in ([], uu____4158)  in
                      let uu____4165 =
                        let uu____4166 = c wp_trivial2  in ([], uu____4166)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___342_4116.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___342_4116.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___342_4116.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___342_4116.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___342_4116.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___342_4116.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___342_4116.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____4117;
                        FStar_Syntax_Syntax.ite_wp = uu____4125;
                        FStar_Syntax_Syntax.stronger = uu____4133;
                        FStar_Syntax_Syntax.close_wp = uu____4141;
                        FStar_Syntax_Syntax.assume_p = uu____4149;
                        FStar_Syntax_Syntax.null_wp = uu____4157;
                        FStar_Syntax_Syntax.trivial = uu____4165;
                        FStar_Syntax_Syntax.repr =
                          (uu___342_4116.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___342_4116.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___342_4116.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___342_4116.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___342_4116.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4088, uu____4115)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___347_4190 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___347_4190.subst);
        tc_const = (uu___347_4190.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4211 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4230 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4250) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4264  ->
                match uu___0_4264 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4267 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4269 ->
        let uu____4270 =
          let uu____4276 =
            let uu____4278 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4278
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4276)  in
        FStar_Errors.raise_error uu____4270 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4288  ->
    match uu___1_4288 with
    | N t ->
        let uu____4291 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4291
    | M t ->
        let uu____4295 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4295
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4304,c) -> nm_of_comp c
    | uu____4326 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4339 = nm_of_comp c  in
    match uu____4339 with | M uu____4341 -> true | N uu____4343 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4354 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4370 =
        let uu____4379 =
          let uu____4386 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4386  in
        [uu____4379]  in
      let uu____4405 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4370 uu____4405  in
    let uu____4408 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4408
  
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
        let uu____4450 =
          let uu____4451 =
            let uu____4466 =
              let uu____4475 =
                let uu____4482 =
                  let uu____4483 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4483  in
                let uu____4484 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4482, uu____4484)  in
              [uu____4475]  in
            let uu____4502 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4466, uu____4502)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4451  in
        mk1 uu____4450

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4542) ->
          let binders1 =
            FStar_List.map
              (fun uu____4588  ->
                 match uu____4588 with
                 | (bv,aqual) ->
                     let uu____4607 =
                       let uu___397_4608 = bv  in
                       let uu____4609 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___397_4608.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___397_4608.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4609
                       }  in
                     (uu____4607, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4614,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4616);
                             FStar_Syntax_Syntax.pos = uu____4617;
                             FStar_Syntax_Syntax.vars = uu____4618;_})
               ->
               let uu____4647 =
                 let uu____4648 =
                   let uu____4663 =
                     let uu____4666 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4666  in
                   (binders1, uu____4663)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4648  in
               mk1 uu____4647
           | uu____4677 ->
               let uu____4678 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4678 with
                | N hn ->
                    let uu____4680 =
                      let uu____4681 =
                        let uu____4696 =
                          let uu____4699 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4699  in
                        (binders1, uu____4696)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4681  in
                    mk1 uu____4680
                | M a ->
                    let uu____4711 =
                      let uu____4712 =
                        let uu____4727 =
                          let uu____4736 =
                            let uu____4745 =
                              let uu____4752 =
                                let uu____4753 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4753  in
                              let uu____4754 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4752, uu____4754)  in
                            [uu____4745]  in
                          FStar_List.append binders1 uu____4736  in
                        let uu____4778 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4727, uu____4778)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4712  in
                    mk1 uu____4711))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4872 = f x  in
                    FStar_Util.string_builder_append strb uu____4872);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4881 = f x1  in
                         FStar_Util.string_builder_append strb uu____4881))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4885 =
              let uu____4891 =
                let uu____4893 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4895 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4893 uu____4895
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4891)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4885  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4917 =
              let uu____4918 = FStar_Syntax_Subst.compress ty  in
              uu____4918.FStar_Syntax_Syntax.n  in
            match uu____4917 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4944 =
                  let uu____4946 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4946  in
                if uu____4944
                then false
                else
                  (try
                     (fun uu___446_4963  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4987 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4987 s  in
                              let uu____4990 =
                                let uu____4992 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4992  in
                              if uu____4990
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4998 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4998 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5023  ->
                                          match uu____5023 with
                                          | (bv,uu____5035) ->
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
            | uu____5063 ->
                ((let uu____5065 =
                    let uu____5071 =
                      let uu____5073 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5073
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5071)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5065);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5089 =
              let uu____5090 = FStar_Syntax_Subst.compress head2  in
              uu____5090.FStar_Syntax_Syntax.n  in
            match uu____5089 with
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
                  (let uu____5096 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5096)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5099 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5099 with
                 | ((uu____5109,ty),uu____5111) ->
                     let uu____5116 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5116
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5129 =
                         let uu____5130 = FStar_Syntax_Subst.compress res  in
                         uu____5130.FStar_Syntax_Syntax.n  in
                       (match uu____5129 with
                        | FStar_Syntax_Syntax.Tm_app uu____5134 -> true
                        | uu____5152 ->
                            ((let uu____5154 =
                                let uu____5160 =
                                  let uu____5162 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5162
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5160)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5154);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5170 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5172 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5175) ->
                is_valid_application t2
            | uu____5180 -> false  in
          let uu____5182 = is_valid_application head1  in
          if uu____5182
          then
            let uu____5185 =
              let uu____5186 =
                let uu____5203 =
                  FStar_List.map
                    (fun uu____5232  ->
                       match uu____5232 with
                       | (t2,qual) ->
                           let uu____5257 = star_type' env t2  in
                           (uu____5257, qual)) args
                   in
                (head1, uu____5203)  in
              FStar_Syntax_Syntax.Tm_app uu____5186  in
            mk1 uu____5185
          else
            (let uu____5274 =
               let uu____5280 =
                 let uu____5282 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5282
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5280)  in
             FStar_Errors.raise_err uu____5274)
      | FStar_Syntax_Syntax.Tm_bvar uu____5286 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5287 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5288 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5289 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5317 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5317 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___518_5325 = env  in
                 let uu____5326 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5326;
                   subst = (uu___518_5325.subst);
                   tc_const = (uu___518_5325.tc_const)
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
               ((let uu___533_5353 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___533_5353.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___533_5353.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5360 =
            let uu____5361 =
              let uu____5368 = star_type' env t2  in (uu____5368, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5361  in
          mk1 uu____5360
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5420 =
            let uu____5421 =
              let uu____5448 = star_type' env e  in
              let uu____5451 =
                let uu____5468 =
                  let uu____5477 = star_type' env t2  in
                  FStar_Util.Inl uu____5477  in
                (uu____5468, FStar_Pervasives_Native.None)  in
              (uu____5448, uu____5451, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5421  in
          mk1 uu____5420
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5565 =
            let uu____5566 =
              let uu____5593 = star_type' env e  in
              let uu____5596 =
                let uu____5613 =
                  let uu____5622 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5622  in
                (uu____5613, FStar_Pervasives_Native.None)  in
              (uu____5593, uu____5596, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5566  in
          mk1 uu____5565
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5663,(uu____5664,FStar_Pervasives_Native.Some uu____5665),uu____5666)
          ->
          let uu____5715 =
            let uu____5721 =
              let uu____5723 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5723
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5721)  in
          FStar_Errors.raise_err uu____5715
      | FStar_Syntax_Syntax.Tm_refine uu____5727 ->
          let uu____5734 =
            let uu____5740 =
              let uu____5742 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5742
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5740)  in
          FStar_Errors.raise_err uu____5734
      | FStar_Syntax_Syntax.Tm_uinst uu____5746 ->
          let uu____5753 =
            let uu____5759 =
              let uu____5761 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5761
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5759)  in
          FStar_Errors.raise_err uu____5753
      | FStar_Syntax_Syntax.Tm_quoted uu____5765 ->
          let uu____5772 =
            let uu____5778 =
              let uu____5780 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5780
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5778)  in
          FStar_Errors.raise_err uu____5772
      | FStar_Syntax_Syntax.Tm_constant uu____5784 ->
          let uu____5785 =
            let uu____5791 =
              let uu____5793 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5793
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5791)  in
          FStar_Errors.raise_err uu____5785
      | FStar_Syntax_Syntax.Tm_match uu____5797 ->
          let uu____5820 =
            let uu____5826 =
              let uu____5828 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5828
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5826)  in
          FStar_Errors.raise_err uu____5820
      | FStar_Syntax_Syntax.Tm_let uu____5832 ->
          let uu____5846 =
            let uu____5852 =
              let uu____5854 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5854
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5852)  in
          FStar_Errors.raise_err uu____5846
      | FStar_Syntax_Syntax.Tm_uvar uu____5858 ->
          let uu____5871 =
            let uu____5877 =
              let uu____5879 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5879
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5877)  in
          FStar_Errors.raise_err uu____5871
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5883 =
            let uu____5889 =
              let uu____5891 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5891
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5889)  in
          FStar_Errors.raise_err uu____5883
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5896 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5896
      | FStar_Syntax_Syntax.Tm_delayed uu____5899 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_5931  ->
    match uu___3_5931 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_5942  ->
                match uu___2_5942 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5945 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5955 =
      let uu____5956 = FStar_Syntax_Subst.compress t  in
      uu____5956.FStar_Syntax_Syntax.n  in
    match uu____5955 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5988 =
            let uu____5989 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5989  in
          is_C uu____5988  in
        if r
        then
          ((let uu____6013 =
              let uu____6015 =
                FStar_List.for_all
                  (fun uu____6026  ->
                     match uu____6026 with | (h,uu____6035) -> is_C h) args
                 in
              Prims.op_Negation uu____6015  in
            if uu____6013 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6048 =
              let uu____6050 =
                FStar_List.for_all
                  (fun uu____6062  ->
                     match uu____6062 with
                     | (h,uu____6071) ->
                         let uu____6076 = is_C h  in
                         Prims.op_Negation uu____6076) args
                 in
              Prims.op_Negation uu____6050  in
            if uu____6048 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6105 = nm_of_comp comp  in
        (match uu____6105 with
         | M t1 ->
             ((let uu____6109 = is_C t1  in
               if uu____6109 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6118) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6124) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6130,uu____6131) -> is_C t1
    | uu____6172 -> false
  
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
          let uu____6208 =
            let uu____6209 =
              let uu____6226 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6229 =
                let uu____6240 =
                  let uu____6249 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6249)  in
                [uu____6240]  in
              (uu____6226, uu____6229)  in
            FStar_Syntax_Syntax.Tm_app uu____6209  in
          mk1 uu____6208  in
        let uu____6285 =
          let uu____6286 = FStar_Syntax_Syntax.mk_binder p  in [uu____6286]
           in
        FStar_Syntax_Util.abs uu____6285 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6311  ->
    match uu___4_6311 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6314 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6552 =
          match uu____6552 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6589 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6592 =
                       let uu____6594 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6594  in
                     Prims.op_Negation uu____6592)
                   in
                if uu____6589
                then
                  let uu____6596 =
                    let uu____6602 =
                      let uu____6604 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6606 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6608 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6604 uu____6606 uu____6608
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6602)  in
                  FStar_Errors.raise_err uu____6596
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6633 = mk_return env t1 s_e  in
                     ((M t1), uu____6633, u_e)))
               | (M t1,N t2) ->
                   let uu____6640 =
                     let uu____6646 =
                       let uu____6648 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6650 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6652 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6648 uu____6650 uu____6652
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6646)
                      in
                   FStar_Errors.raise_err uu____6640)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_6704 =
            match uu___5_6704 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6720 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6741 =
                let uu____6747 =
                  let uu____6749 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6749
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6747)  in
              FStar_Errors.raise_error uu____6741 e2.FStar_Syntax_Syntax.pos
          | M uu____6759 ->
              let uu____6760 = check env1 e2 context_nm  in
              strip_m uu____6760
           in
        let uu____6767 =
          let uu____6768 = FStar_Syntax_Subst.compress e  in
          uu____6768.FStar_Syntax_Syntax.n  in
        match uu____6767 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6777 ->
            let uu____6778 = infer env e  in return_if uu____6778
        | FStar_Syntax_Syntax.Tm_name uu____6785 ->
            let uu____6786 = infer env e  in return_if uu____6786
        | FStar_Syntax_Syntax.Tm_fvar uu____6793 ->
            let uu____6794 = infer env e  in return_if uu____6794
        | FStar_Syntax_Syntax.Tm_abs uu____6801 ->
            let uu____6820 = infer env e  in return_if uu____6820
        | FStar_Syntax_Syntax.Tm_constant uu____6827 ->
            let uu____6828 = infer env e  in return_if uu____6828
        | FStar_Syntax_Syntax.Tm_quoted uu____6835 ->
            let uu____6842 = infer env e  in return_if uu____6842
        | FStar_Syntax_Syntax.Tm_app uu____6849 ->
            let uu____6866 = infer env e  in return_if uu____6866
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6874 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6874 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6939) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6945) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6951,uu____6952) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6993 ->
            let uu____7007 =
              let uu____7009 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7009  in
            failwith uu____7007
        | FStar_Syntax_Syntax.Tm_type uu____7018 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7026 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7048 ->
            let uu____7055 =
              let uu____7057 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7057  in
            failwith uu____7055
        | FStar_Syntax_Syntax.Tm_uvar uu____7066 ->
            let uu____7079 =
              let uu____7081 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7081  in
            failwith uu____7079
        | FStar_Syntax_Syntax.Tm_delayed uu____7090 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7120 =
              let uu____7122 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7122  in
            failwith uu____7120

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
      let uu____7152 =
        let uu____7153 = FStar_Syntax_Subst.compress e  in
        uu____7153.FStar_Syntax_Syntax.n  in
      match uu____7152 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7172 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7172
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7223;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7224;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7230 =
                  let uu___768_7231 = rc  in
                  let uu____7232 =
                    let uu____7237 =
                      let uu____7240 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7240  in
                    FStar_Pervasives_Native.Some uu____7237  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___768_7231.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7232;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___768_7231.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7230
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___774_7252 = env  in
            let uu____7253 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7253;
              subst = (uu___774_7252.subst);
              tc_const = (uu___774_7252.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7279  ->
                 match uu____7279 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___781_7302 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___781_7302.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___781_7302.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7303 =
            FStar_List.fold_left
              (fun uu____7334  ->
                 fun uu____7335  ->
                   match (uu____7334, uu____7335) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7393 = is_C c  in
                       if uu____7393
                       then
                         let xw =
                           let uu____7403 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7403
                            in
                         let x =
                           let uu___793_7406 = bv  in
                           let uu____7407 =
                             let uu____7410 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7410  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___793_7406.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___793_7406.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7407
                           }  in
                         let env3 =
                           let uu___796_7412 = env2  in
                           let uu____7413 =
                             let uu____7416 =
                               let uu____7417 =
                                 let uu____7424 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7424)  in
                               FStar_Syntax_Syntax.NT uu____7417  in
                             uu____7416 :: (env2.subst)  in
                           {
                             tcenv = (uu___796_7412.tcenv);
                             subst = uu____7413;
                             tc_const = (uu___796_7412.tc_const)
                           }  in
                         let uu____7429 =
                           let uu____7432 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7433 =
                             let uu____7436 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7436 :: acc  in
                           uu____7432 :: uu____7433  in
                         (env3, uu____7429)
                       else
                         (let x =
                            let uu___799_7442 = bv  in
                            let uu____7443 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___799_7442.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___799_7442.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7443
                            }  in
                          let uu____7446 =
                            let uu____7449 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7449 :: acc  in
                          (env2, uu____7446))) (env1, []) binders1
             in
          (match uu____7303 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7469 =
                 let check_what =
                   let uu____7495 = is_monadic rc_opt1  in
                   if uu____7495 then check_m else check_n  in
                 let uu____7512 = check_what env2 body1  in
                 match uu____7512 with
                 | (t,s_body,u_body) ->
                     let uu____7532 =
                       let uu____7535 =
                         let uu____7536 = is_monadic rc_opt1  in
                         if uu____7536 then M t else N t  in
                       comp_of_nm uu____7535  in
                     (uu____7532, s_body, u_body)
                  in
               (match uu____7469 with
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
                                 let uu____7576 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7582  ->
                                           match uu___6_7582 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7585 -> false))
                                    in
                                 if uu____7576
                                 then
                                   let uu____7588 =
                                     FStar_List.filter
                                       (fun uu___7_7592  ->
                                          match uu___7_7592 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7595 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7588
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7606 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7612  ->
                                         match uu___8_7612 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7615 -> false))
                                  in
                               if uu____7606
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7624  ->
                                        match uu___9_7624 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7627 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7629 =
                                   let uu____7630 =
                                     let uu____7635 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7635
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7630 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7629
                               else
                                 (let uu____7642 =
                                    let uu___840_7643 = rc  in
                                    let uu____7644 =
                                      let uu____7649 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7649
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___840_7643.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7644;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___840_7643.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7642))
                       in
                    let uu____7654 =
                      let comp1 =
                        let uu____7662 = is_monadic rc_opt1  in
                        let uu____7664 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7662 uu____7664
                         in
                      let uu____7665 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7665,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7654 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7703 =
                             let uu____7704 =
                               let uu____7723 =
                                 let uu____7726 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7726 s_rc_opt  in
                               (s_binders1, s_body1, uu____7723)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7704  in
                           mk1 uu____7703  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7746 =
                             let uu____7747 =
                               let uu____7766 =
                                 let uu____7769 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7769 u_rc_opt  in
                               (u_binders2, u_body2, uu____7766)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7747  in
                           mk1 uu____7746  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7785;_};
            FStar_Syntax_Syntax.fv_delta = uu____7786;
            FStar_Syntax_Syntax.fv_qual = uu____7787;_}
          ->
          let uu____7790 =
            let uu____7795 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7795  in
          (match uu____7790 with
           | (uu____7826,t) ->
               let uu____7828 =
                 let uu____7829 = normalize1 t  in N uu____7829  in
               (uu____7828, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7830;
             FStar_Syntax_Syntax.vars = uu____7831;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7910 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7910 with
           | (unary_op1,uu____7934) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8005;
             FStar_Syntax_Syntax.vars = uu____8006;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8102 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8102 with
           | (unary_op1,uu____8126) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8205;
             FStar_Syntax_Syntax.vars = uu____8206;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8244 = infer env a  in
          (match uu____8244 with
           | (t,s,u) ->
               let uu____8260 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8260 with
                | (head1,uu____8284) ->
                    let uu____8309 =
                      let uu____8310 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8310  in
                    let uu____8311 =
                      let uu____8312 =
                        let uu____8313 =
                          let uu____8330 =
                            let uu____8341 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8341]  in
                          (head1, uu____8330)  in
                        FStar_Syntax_Syntax.Tm_app uu____8313  in
                      mk1 uu____8312  in
                    let uu____8378 =
                      let uu____8379 =
                        let uu____8380 =
                          let uu____8397 =
                            let uu____8408 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8408]  in
                          (head1, uu____8397)  in
                        FStar_Syntax_Syntax.Tm_app uu____8380  in
                      mk1 uu____8379  in
                    (uu____8309, uu____8311, uu____8378)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8445;
             FStar_Syntax_Syntax.vars = uu____8446;_},(a1,uu____8448)::a2::[])
          ->
          let uu____8504 = infer env a1  in
          (match uu____8504 with
           | (t,s,u) ->
               let uu____8520 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8520 with
                | (head1,uu____8544) ->
                    let uu____8569 =
                      let uu____8570 =
                        let uu____8571 =
                          let uu____8588 =
                            let uu____8599 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8599; a2]  in
                          (head1, uu____8588)  in
                        FStar_Syntax_Syntax.Tm_app uu____8571  in
                      mk1 uu____8570  in
                    let uu____8644 =
                      let uu____8645 =
                        let uu____8646 =
                          let uu____8663 =
                            let uu____8674 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8674; a2]  in
                          (head1, uu____8663)  in
                        FStar_Syntax_Syntax.Tm_app uu____8646  in
                      mk1 uu____8645  in
                    (t, uu____8569, uu____8644)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8719;
             FStar_Syntax_Syntax.vars = uu____8720;_},uu____8721)
          ->
          let uu____8746 =
            let uu____8752 =
              let uu____8754 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8754
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8752)  in
          FStar_Errors.raise_error uu____8746 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8764;
             FStar_Syntax_Syntax.vars = uu____8765;_},uu____8766)
          ->
          let uu____8791 =
            let uu____8797 =
              let uu____8799 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8799
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8797)  in
          FStar_Errors.raise_error uu____8791 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8835 = check_n env head1  in
          (match uu____8835 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8858 =
                   let uu____8859 = FStar_Syntax_Subst.compress t  in
                   uu____8859.FStar_Syntax_Syntax.n  in
                 match uu____8858 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8863 -> true
                 | uu____8879 -> false  in
               let rec flatten1 t =
                 let uu____8901 =
                   let uu____8902 = FStar_Syntax_Subst.compress t  in
                   uu____8902.FStar_Syntax_Syntax.n  in
                 match uu____8901 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8921);
                                FStar_Syntax_Syntax.pos = uu____8922;
                                FStar_Syntax_Syntax.vars = uu____8923;_})
                     when is_arrow t1 ->
                     let uu____8952 = flatten1 t1  in
                     (match uu____8952 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9052,uu____9053)
                     -> flatten1 e1
                 | uu____9094 ->
                     let uu____9095 =
                       let uu____9101 =
                         let uu____9103 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9103
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9101)  in
                     FStar_Errors.raise_err uu____9095
                  in
               let uu____9121 = flatten1 t_head  in
               (match uu____9121 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9196 =
                          let uu____9202 =
                            let uu____9204 = FStar_Util.string_of_int n1  in
                            let uu____9206 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9208 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9204 uu____9206 uu____9208
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9202)
                           in
                        FStar_Errors.raise_err uu____9196)
                     else ();
                     (let uu____9214 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9214 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9267 args1 =
                            match uu____9267 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9367 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9367
                                 | (binders3,[]) ->
                                     let uu____9405 =
                                       let uu____9406 =
                                         let uu____9409 =
                                           let uu____9410 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9410
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9409
                                          in
                                       uu____9406.FStar_Syntax_Syntax.n  in
                                     (match uu____9405 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9443 =
                                            let uu____9444 =
                                              let uu____9445 =
                                                let uu____9460 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9460)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9445
                                               in
                                            mk1 uu____9444  in
                                          N uu____9443
                                      | uu____9473 -> failwith "wat?")
                                 | ([],uu____9475::uu____9476) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9529)::binders3,(arg,uu____9532)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9619 = FStar_List.splitAt n' binders1  in
                          (match uu____9619 with
                           | (binders2,uu____9653) ->
                               let uu____9686 =
                                 let uu____9709 =
                                   FStar_List.map2
                                     (fun uu____9771  ->
                                        fun uu____9772  ->
                                          match (uu____9771, uu____9772) with
                                          | ((bv,uu____9820),(arg,q)) ->
                                              let uu____9849 =
                                                let uu____9850 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9850.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9849 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9871 ->
                                                   let uu____9872 =
                                                     let uu____9879 =
                                                       star_type' env arg  in
                                                     (uu____9879, q)  in
                                                   (uu____9872, [(arg, q)])
                                               | uu____9916 ->
                                                   let uu____9917 =
                                                     check_n env arg  in
                                                   (match uu____9917 with
                                                    | (uu____9942,s_arg,u_arg)
                                                        ->
                                                        let uu____9945 =
                                                          let uu____9954 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9954
                                                          then
                                                            let uu____9965 =
                                                              let uu____9972
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9972, q)
                                                               in
                                                            [uu____9965;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9945))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9709  in
                               (match uu____9686 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10100 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10113 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10100, uu____10113)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10182) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10188) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10194,uu____10195) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10237 =
            let uu____10238 = env.tc_const c  in N uu____10238  in
          (uu____10237, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10245 ->
          let uu____10259 =
            let uu____10261 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10261  in
          failwith uu____10259
      | FStar_Syntax_Syntax.Tm_type uu____10270 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10278 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10300 ->
          let uu____10307 =
            let uu____10309 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10309  in
          failwith uu____10307
      | FStar_Syntax_Syntax.Tm_uvar uu____10318 ->
          let uu____10331 =
            let uu____10333 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10333  in
          failwith uu____10331
      | FStar_Syntax_Syntax.Tm_delayed uu____10342 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10372 =
            let uu____10374 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10374  in
          failwith uu____10372

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
          let uu____10423 = check_n env e0  in
          match uu____10423 with
          | (uu____10436,s_e0,u_e0) ->
              let uu____10439 =
                let uu____10468 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10529 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10529 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1115_10571 = env  in
                             let uu____10572 =
                               let uu____10573 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10573
                                in
                             {
                               tcenv = uu____10572;
                               subst = (uu___1115_10571.subst);
                               tc_const = (uu___1115_10571.tc_const)
                             }  in
                           let uu____10576 = f env1 body  in
                           (match uu____10576 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10648 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10468  in
              (match uu____10439 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10754 = FStar_List.hd nms  in
                     match uu____10754 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10763  ->
                          match uu___10_10763 with
                          | M uu____10765 -> true
                          | uu____10767 -> false) nms
                      in
                   let uu____10769 =
                     let uu____10806 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10896  ->
                              match uu____10896 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11080 =
                                         check env original_body (M t2)  in
                                       (match uu____11080 with
                                        | (uu____11117,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11156,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10806  in
                   (match uu____10769 with
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
                              (fun uu____11345  ->
                                 match uu____11345 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11396 =
                                         let uu____11397 =
                                           let uu____11414 =
                                             let uu____11425 =
                                               let uu____11434 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11437 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11434, uu____11437)  in
                                             [uu____11425]  in
                                           (s_body, uu____11414)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11397
                                          in
                                       mk1 uu____11396  in
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
                            let uu____11572 =
                              let uu____11573 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11573]  in
                            let uu____11592 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11572 uu____11592
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11616 =
                              let uu____11625 =
                                let uu____11632 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11632
                                 in
                              [uu____11625]  in
                            let uu____11651 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11616 uu____11651
                             in
                          let uu____11654 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11693 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11654, uu____11693)
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
                           let uu____11803 =
                             let uu____11804 =
                               let uu____11805 =
                                 let uu____11832 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11832,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11805
                                in
                             mk1 uu____11804  in
                           let uu____11891 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11803, uu____11891))))

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
              let uu____11956 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11956]  in
            let uu____11975 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11975 with
            | (x_binders1,e21) ->
                let uu____11988 = infer env e1  in
                (match uu____11988 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12005 = is_C t1  in
                       if uu____12005
                       then
                         let uu___1201_12008 = binding  in
                         let uu____12009 =
                           let uu____12012 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12012  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1201_12008.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1201_12008.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12009;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1201_12008.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1201_12008.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1201_12008.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1201_12008.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1204_12016 = env  in
                       let uu____12017 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1206_12019 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1206_12019.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1206_12019.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12017;
                         subst = (uu___1204_12016.subst);
                         tc_const = (uu___1204_12016.tc_const)
                       }  in
                     let uu____12020 = proceed env1 e21  in
                     (match uu____12020 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1213_12037 = binding  in
                            let uu____12038 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1213_12037.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1213_12037.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12038;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1213_12037.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1213_12037.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1213_12037.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1213_12037.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12041 =
                            let uu____12042 =
                              let uu____12043 =
                                let uu____12057 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1216_12074 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1216_12074.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1216_12074.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1216_12074.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1216_12074.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1216_12074.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1216_12074.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12057)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12043  in
                            mk1 uu____12042  in
                          let uu____12075 =
                            let uu____12076 =
                              let uu____12077 =
                                let uu____12091 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1218_12108 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1218_12108.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1218_12108.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1218_12108.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1218_12108.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1218_12108.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1218_12108.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12091)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12077  in
                            mk1 uu____12076  in
                          (nm_rec, uu____12041, uu____12075))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1225_12113 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1225_12113.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1225_12113.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1225_12113.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1225_12113.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1225_12113.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1228_12115 = env  in
                       let uu____12116 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1230_12118 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1230_12118.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1230_12118.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12116;
                         subst = (uu___1228_12115.subst);
                         tc_const = (uu___1228_12115.tc_const)
                       }  in
                     let uu____12119 = ensure_m env1 e21  in
                     (match uu____12119 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12143 =
                              let uu____12144 =
                                let uu____12161 =
                                  let uu____12172 =
                                    let uu____12181 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12184 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12181, uu____12184)  in
                                  [uu____12172]  in
                                (s_e2, uu____12161)  in
                              FStar_Syntax_Syntax.Tm_app uu____12144  in
                            mk1 uu____12143  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12226 =
                              let uu____12227 =
                                let uu____12244 =
                                  let uu____12255 =
                                    let uu____12264 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12264)  in
                                  [uu____12255]  in
                                (s_e1, uu____12244)  in
                              FStar_Syntax_Syntax.Tm_app uu____12227  in
                            mk1 uu____12226  in
                          let uu____12300 =
                            let uu____12301 =
                              let uu____12302 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12302]  in
                            FStar_Syntax_Util.abs uu____12301 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12321 =
                            let uu____12322 =
                              let uu____12323 =
                                let uu____12337 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1242_12354 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1242_12354.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1242_12354.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1242_12354.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1242_12354.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1242_12354.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1242_12354.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12337)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12323  in
                            mk1 uu____12322  in
                          ((M t2), uu____12300, uu____12321)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12364 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12364  in
      let uu____12365 = check env e mn  in
      match uu____12365 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12381 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12404 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12404  in
      let uu____12405 = check env e mn  in
      match uu____12405 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12421 -> failwith "[check_m]: impossible"

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
        (let uu____12454 =
           let uu____12456 = is_C c  in Prims.op_Negation uu____12456  in
         if uu____12454 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12470 =
           let uu____12471 = FStar_Syntax_Subst.compress c  in
           uu____12471.FStar_Syntax_Syntax.n  in
         match uu____12470 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12500 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12500 with
              | (wp_head,wp_args) ->
                  ((let uu____12544 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12563 =
                           let uu____12565 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12565
                            in
                         Prims.op_Negation uu____12563)
                       in
                    if uu____12544 then failwith "mismatch" else ());
                   (let uu____12578 =
                      let uu____12579 =
                        let uu____12596 =
                          FStar_List.map2
                            (fun uu____12634  ->
                               fun uu____12635  ->
                                 match (uu____12634, uu____12635) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12697 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12697
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12706 =
                                         let uu____12708 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12708 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12706
                                       then
                                         let uu____12710 =
                                           let uu____12716 =
                                             let uu____12718 =
                                               print_implicit q  in
                                             let uu____12720 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12718 uu____12720
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12716)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12710
                                       else ());
                                      (let uu____12726 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12726, q)))) args wp_args
                           in
                        (head1, uu____12596)  in
                      FStar_Syntax_Syntax.Tm_app uu____12579  in
                    mk1 uu____12578)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12772 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12772 with
              | (binders_orig,comp1) ->
                  let uu____12779 =
                    let uu____12796 =
                      FStar_List.map
                        (fun uu____12836  ->
                           match uu____12836 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12864 = is_C h  in
                               if uu____12864
                               then
                                 let w' =
                                   let uu____12880 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12880
                                    in
                                 let uu____12882 =
                                   let uu____12891 =
                                     let uu____12900 =
                                       let uu____12907 =
                                         let uu____12908 =
                                           let uu____12909 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12909  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12908
                                          in
                                       (uu____12907, q)  in
                                     [uu____12900]  in
                                   (w', q) :: uu____12891  in
                                 (w', uu____12882)
                               else
                                 (let x =
                                    let uu____12943 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____12943
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12796  in
                  (match uu____12779 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13017 =
                           let uu____13020 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13020
                            in
                         FStar_Syntax_Subst.subst_comp uu____13017 comp1  in
                       let app =
                         let uu____13024 =
                           let uu____13025 =
                             let uu____13042 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13061 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13062 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13061, uu____13062)) bvs
                                in
                             (wp, uu____13042)  in
                           FStar_Syntax_Syntax.Tm_app uu____13025  in
                         mk1 uu____13024  in
                       let comp3 =
                         let uu____13077 = type_of_comp comp2  in
                         let uu____13078 = is_monadic_comp comp2  in
                         trans_G env uu____13077 uu____13078 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13081,uu____13082) ->
             trans_F_ env e wp
         | uu____13123 -> failwith "impossible trans_F_")

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
            let uu____13131 =
              let uu____13132 = star_type' env h  in
              let uu____13135 =
                let uu____13146 =
                  let uu____13155 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13155)  in
                [uu____13146]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13132;
                FStar_Syntax_Syntax.effect_args = uu____13135;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13131
          else
            (let uu____13181 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13181)

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
    fun t  -> let uu____13202 = n env.tcenv t  in star_type' env uu____13202
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13222 = n env.tcenv t  in check_n env uu____13222
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13239 = n env.tcenv c  in
        let uu____13240 = n env.tcenv wp  in
        trans_F_ env uu____13239 uu____13240
  