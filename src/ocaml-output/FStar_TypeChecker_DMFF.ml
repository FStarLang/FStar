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
                                  FStar_Syntax_Util.mk_app l_and uu____1946
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
                  let wp_assert1 =
                    let uu____2020 = mk_lid "wp_assert"  in
                    register env1 uu____2020 wp_assert  in
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
                      let uu____2037 =
                        let uu____2048 =
                          let uu____2051 =
                            let uu____2052 =
                              let uu____2063 =
                                let uu____2066 =
                                  let uu____2067 =
                                    let uu____2078 =
                                      let uu____2087 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2087
                                       in
                                    [uu____2078]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____2067
                                   in
                                [uu____2066]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____2063
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2052  in
                          let uu____2112 =
                            let uu____2115 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2115]  in
                          uu____2051 :: uu____2112  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2048
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2037  in
                    let uu____2124 =
                      let uu____2125 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2125  in
                    FStar_Syntax_Util.abs uu____2124 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2141 = mk_lid "wp_assume"  in
                    register env1 uu____2141 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2154 =
                        let uu____2163 =
                          let uu____2170 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2170  in
                        [uu____2163]  in
                      let uu____2183 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2154 uu____2183  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2191 =
                        let uu____2202 =
                          let uu____2205 =
                            let uu____2206 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2206  in
                          let uu____2225 =
                            let uu____2228 =
                              let uu____2229 =
                                let uu____2240 =
                                  let uu____2243 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2243]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2240
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2229  in
                            [uu____2228]  in
                          uu____2205 :: uu____2225  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2202
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2191  in
                    let uu____2260 =
                      let uu____2261 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2261  in
                    FStar_Syntax_Util.abs uu____2260 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2277 = mk_lid "wp_close"  in
                    register env1 uu____2277 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2288 =
                      let uu____2289 =
                        let uu____2290 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2290
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2289  in
                    FStar_Pervasives_Native.Some uu____2288  in
                  let mk_forall1 x body =
                    let uu____2302 =
                      let uu____2309 =
                        let uu____2310 =
                          let uu____2327 =
                            let uu____2338 =
                              let uu____2347 =
                                let uu____2348 =
                                  let uu____2349 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2349]  in
                                FStar_Syntax_Util.abs uu____2348 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2347  in
                            [uu____2338]  in
                          (FStar_Syntax_Util.tforall, uu____2327)  in
                        FStar_Syntax_Syntax.Tm_app uu____2310  in
                      FStar_Syntax_Syntax.mk uu____2309  in
                    uu____2302 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2407 =
                      let uu____2408 = FStar_Syntax_Subst.compress t  in
                      uu____2408.FStar_Syntax_Syntax.n  in
                    match uu____2407 with
                    | FStar_Syntax_Syntax.Tm_type uu____2412 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2445  ->
                              match uu____2445 with
                              | (b,uu____2454) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2459 -> true  in
                  let rec is_monotonic t =
                    let uu____2472 =
                      let uu____2473 = FStar_Syntax_Subst.compress t  in
                      uu____2473.FStar_Syntax_Syntax.n  in
                    match uu____2472 with
                    | FStar_Syntax_Syntax.Tm_type uu____2477 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2510  ->
                              match uu____2510 with
                              | (b,uu____2519) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2524 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2598 =
                      let uu____2599 = FStar_Syntax_Subst.compress t1  in
                      uu____2599.FStar_Syntax_Syntax.n  in
                    match uu____2598 with
                    | FStar_Syntax_Syntax.Tm_type uu____2604 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2607);
                                      FStar_Syntax_Syntax.pos = uu____2608;
                                      FStar_Syntax_Syntax.vars = uu____2609;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2653 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2653
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2663 =
                              let uu____2666 =
                                let uu____2677 =
                                  let uu____2686 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2686  in
                                [uu____2677]  in
                              FStar_Syntax_Util.mk_app x uu____2666  in
                            let uu____2703 =
                              let uu____2706 =
                                let uu____2717 =
                                  let uu____2726 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2726  in
                                [uu____2717]  in
                              FStar_Syntax_Util.mk_app y uu____2706  in
                            mk_rel1 b uu____2663 uu____2703  in
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
                             let uu____2750 =
                               let uu____2753 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2756 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2753 uu____2756  in
                             let uu____2759 =
                               let uu____2762 =
                                 let uu____2765 =
                                   let uu____2776 =
                                     let uu____2785 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2785
                                      in
                                   [uu____2776]  in
                                 FStar_Syntax_Util.mk_app x uu____2765  in
                               let uu____2802 =
                                 let uu____2805 =
                                   let uu____2816 =
                                     let uu____2825 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2825
                                      in
                                   [uu____2816]  in
                                 FStar_Syntax_Util.mk_app y uu____2805  in
                               mk_rel1 b uu____2762 uu____2802  in
                             FStar_Syntax_Util.mk_imp uu____2750 uu____2759
                              in
                           let uu____2842 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2842)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2845);
                                      FStar_Syntax_Syntax.pos = uu____2846;
                                      FStar_Syntax_Syntax.vars = uu____2847;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2891 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2891
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2901 =
                              let uu____2904 =
                                let uu____2915 =
                                  let uu____2924 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2924  in
                                [uu____2915]  in
                              FStar_Syntax_Util.mk_app x uu____2904  in
                            let uu____2941 =
                              let uu____2944 =
                                let uu____2955 =
                                  let uu____2964 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2964  in
                                [uu____2955]  in
                              FStar_Syntax_Util.mk_app y uu____2944  in
                            mk_rel1 b uu____2901 uu____2941  in
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
                             let uu____2988 =
                               let uu____2991 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2994 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2991 uu____2994  in
                             let uu____2997 =
                               let uu____3000 =
                                 let uu____3003 =
                                   let uu____3014 =
                                     let uu____3023 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____3023
                                      in
                                   [uu____3014]  in
                                 FStar_Syntax_Util.mk_app x uu____3003  in
                               let uu____3040 =
                                 let uu____3043 =
                                   let uu____3054 =
                                     let uu____3063 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____3063
                                      in
                                   [uu____3054]  in
                                 FStar_Syntax_Util.mk_app y uu____3043  in
                               mk_rel1 b uu____3000 uu____3040  in
                             FStar_Syntax_Util.mk_imp uu____2988 uu____2997
                              in
                           let uu____3080 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____3080)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___242_3119 = t1  in
                          let uu____3120 =
                            let uu____3121 =
                              let uu____3136 =
                                let uu____3139 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3139  in
                              ([binder], uu____3136)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3121  in
                          {
                            FStar_Syntax_Syntax.n = uu____3120;
                            FStar_Syntax_Syntax.pos =
                              (uu___242_3119.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___242_3119.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3162 ->
                        failwith "unhandled arrow"
                    | uu____3180 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____3217 =
                        let uu____3218 = FStar_Syntax_Subst.compress t1  in
                        uu____3218.FStar_Syntax_Syntax.n  in
                      match uu____3217 with
                      | FStar_Syntax_Syntax.Tm_type uu____3221 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3248 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3248
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3269 =
                                let uu____3270 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3270 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3269
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3300 =
                            let uu____3311 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3329  ->
                                     match uu____3329 with
                                     | (t2,q) ->
                                         let uu____3349 = project i x  in
                                         let uu____3352 = project i y  in
                                         mk_stronger t2 uu____3349 uu____3352)
                                args
                               in
                            match uu____3311 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3300 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3406);
                                      FStar_Syntax_Syntax.pos = uu____3407;
                                      FStar_Syntax_Syntax.vars = uu____3408;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3452  ->
                                   match uu____3452 with
                                   | (bv,q) ->
                                       let uu____3466 =
                                         let uu____3468 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3468  in
                                       FStar_Syntax_Syntax.gen_bv uu____3466
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3477 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3477) bvs
                             in
                          let body =
                            let uu____3479 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3482 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3479 uu____3482  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3491);
                                      FStar_Syntax_Syntax.pos = uu____3492;
                                      FStar_Syntax_Syntax.vars = uu____3493;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3537  ->
                                   match uu____3537 with
                                   | (bv,q) ->
                                       let uu____3551 =
                                         let uu____3553 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3553  in
                                       FStar_Syntax_Syntax.gen_bv uu____3551
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3562 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3562) bvs
                             in
                          let body =
                            let uu____3564 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3567 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3564 uu____3567  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3574 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3577 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3580 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3583 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3577 uu____3580 uu____3583  in
                    let uu____3586 =
                      let uu____3587 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3587  in
                    FStar_Syntax_Util.abs uu____3586 body ret_tot_type  in
                  let stronger1 =
                    let uu____3629 = mk_lid "stronger"  in
                    register env1 uu____3629 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3637 = FStar_Util.prefix gamma  in
                    match uu____3637 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3703 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3703
                             in
                          let uu____3708 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3708 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3718 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3718  in
                              let guard_free1 =
                                let uu____3730 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3730  in
                              let pat =
                                let uu____3734 =
                                  let uu____3745 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3745]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3734
                                 in
                              let pattern_guarded_body =
                                let uu____3773 =
                                  let uu____3774 =
                                    let uu____3781 =
                                      let uu____3782 =
                                        let uu____3795 =
                                          let uu____3806 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3806]  in
                                        [uu____3795]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3782
                                       in
                                    (body, uu____3781)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3774  in
                                mk1 uu____3773  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3853 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3862 =
                            let uu____3865 =
                              let uu____3866 =
                                let uu____3869 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3872 =
                                  let uu____3883 = args_of_binders1 wp_args
                                     in
                                  let uu____3886 =
                                    let uu____3889 =
                                      let uu____3890 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3890
                                       in
                                    [uu____3889]  in
                                  FStar_List.append uu____3883 uu____3886  in
                                FStar_Syntax_Util.mk_app uu____3869
                                  uu____3872
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3866  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3865
                             in
                          FStar_Syntax_Util.abs gamma uu____3862
                            ret_gtot_type
                           in
                        let uu____3891 =
                          let uu____3892 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3892  in
                        FStar_Syntax_Util.abs uu____3891 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3908 = mk_lid "ite_wp"  in
                    register env1 uu____3908 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3916 = FStar_Util.prefix gamma  in
                    match uu____3916 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3974 =
                            let uu____3975 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3982 =
                              let uu____3993 =
                                let uu____4002 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____4002  in
                              [uu____3993]  in
                            FStar_Syntax_Util.mk_app uu____3975 uu____3982
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3974
                           in
                        let uu____4019 =
                          let uu____4020 =
                            let uu____4029 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____4029 gamma  in
                          FStar_List.append binders uu____4020  in
                        FStar_Syntax_Util.abs uu____4019 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____4051 = mk_lid "null_wp"  in
                    register env1 uu____4051 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____4064 =
                        let uu____4075 =
                          let uu____4078 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4079 =
                            let uu____4082 =
                              let uu____4083 =
                                let uu____4094 =
                                  let uu____4103 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4103  in
                                [uu____4094]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4083
                               in
                            let uu____4120 =
                              let uu____4123 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4123]  in
                            uu____4082 :: uu____4120  in
                          uu____4078 :: uu____4079  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4075
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____4064  in
                    let uu____4132 =
                      let uu____4133 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4133  in
                    FStar_Syntax_Util.abs uu____4132 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4149 = mk_lid "wp_trivial"  in
                    register env1 uu____4149 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4155 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4155
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4167 =
                      let uu____4168 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4168  in
                    let uu____4194 =
                      let uu___349_4195 = ed  in
                      let uu____4196 =
                        let uu____4197 = c wp_if_then_else2  in
                        ([], uu____4197)  in
                      let uu____4204 =
                        let uu____4205 = c ite_wp2  in ([], uu____4205)  in
                      let uu____4212 =
                        let uu____4213 = c stronger2  in ([], uu____4213)  in
                      let uu____4220 =
                        let uu____4221 = c wp_close2  in ([], uu____4221)  in
                      let uu____4228 =
                        let uu____4229 = c wp_assert2  in ([], uu____4229)
                         in
                      let uu____4236 =
                        let uu____4237 = c wp_assume2  in ([], uu____4237)
                         in
                      let uu____4244 =
                        let uu____4245 = c null_wp2  in ([], uu____4245)  in
                      let uu____4252 =
                        let uu____4253 = c wp_trivial2  in ([], uu____4253)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___349_4195.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___349_4195.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___349_4195.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___349_4195.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___349_4195.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___349_4195.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___349_4195.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____4196;
                        FStar_Syntax_Syntax.ite_wp = uu____4204;
                        FStar_Syntax_Syntax.stronger = uu____4212;
                        FStar_Syntax_Syntax.close_wp = uu____4220;
                        FStar_Syntax_Syntax.assert_p = uu____4228;
                        FStar_Syntax_Syntax.assume_p = uu____4236;
                        FStar_Syntax_Syntax.null_wp = uu____4244;
                        FStar_Syntax_Syntax.trivial = uu____4252;
                        FStar_Syntax_Syntax.repr =
                          (uu___349_4195.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___349_4195.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___349_4195.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___349_4195.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___349_4195.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4167, uu____4194)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___354_4277 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___354_4277.subst);
        tc_const = (uu___354_4277.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4298 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4317 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4337) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4351  ->
                match uu___0_4351 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4354 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4356 ->
        let uu____4357 =
          let uu____4363 =
            let uu____4365 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4365
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4363)  in
        FStar_Errors.raise_error uu____4357 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4375  ->
    match uu___1_4375 with
    | N t ->
        let uu____4378 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4378
    | M t ->
        let uu____4382 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4382
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4391,c) -> nm_of_comp c
    | uu____4413 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4426 = nm_of_comp c  in
    match uu____4426 with | M uu____4428 -> true | N uu____4430 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4441 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4457 =
        let uu____4466 =
          let uu____4473 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4473  in
        [uu____4466]  in
      let uu____4492 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4457 uu____4492  in
    let uu____4495 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4495
  
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
        let uu____4537 =
          let uu____4538 =
            let uu____4553 =
              let uu____4562 =
                let uu____4569 =
                  let uu____4570 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4570  in
                let uu____4571 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4569, uu____4571)  in
              [uu____4562]  in
            let uu____4589 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4553, uu____4589)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4538  in
        mk1 uu____4537

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4629) ->
          let binders1 =
            FStar_List.map
              (fun uu____4675  ->
                 match uu____4675 with
                 | (bv,aqual) ->
                     let uu____4694 =
                       let uu___404_4695 = bv  in
                       let uu____4696 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___404_4695.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___404_4695.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4696
                       }  in
                     (uu____4694, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4701,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4703);
                             FStar_Syntax_Syntax.pos = uu____4704;
                             FStar_Syntax_Syntax.vars = uu____4705;_})
               ->
               let uu____4734 =
                 let uu____4735 =
                   let uu____4750 =
                     let uu____4753 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4753  in
                   (binders1, uu____4750)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4735  in
               mk1 uu____4734
           | uu____4764 ->
               let uu____4765 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4765 with
                | N hn ->
                    let uu____4767 =
                      let uu____4768 =
                        let uu____4783 =
                          let uu____4786 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4786  in
                        (binders1, uu____4783)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4768  in
                    mk1 uu____4767
                | M a ->
                    let uu____4798 =
                      let uu____4799 =
                        let uu____4814 =
                          let uu____4823 =
                            let uu____4832 =
                              let uu____4839 =
                                let uu____4840 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4840  in
                              let uu____4841 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4839, uu____4841)  in
                            [uu____4832]  in
                          FStar_List.append binders1 uu____4823  in
                        let uu____4865 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4814, uu____4865)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4799  in
                    mk1 uu____4798))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4959 = f x  in
                    FStar_Util.string_builder_append strb uu____4959);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4968 = f x1  in
                         FStar_Util.string_builder_append strb uu____4968))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4972 =
              let uu____4978 =
                let uu____4980 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4982 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4980 uu____4982
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4978)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4972  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____5004 =
              let uu____5005 = FStar_Syntax_Subst.compress ty  in
              uu____5005.FStar_Syntax_Syntax.n  in
            match uu____5004 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5031 =
                  let uu____5033 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____5033  in
                if uu____5031
                then false
                else
                  (try
                     (fun uu___453_5050  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____5074 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____5074 s  in
                              let uu____5077 =
                                let uu____5079 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____5079  in
                              if uu____5077
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____5085 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____5085 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5110  ->
                                          match uu____5110 with
                                          | (bv,uu____5122) ->
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
            | uu____5150 ->
                ((let uu____5152 =
                    let uu____5158 =
                      let uu____5160 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5160
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5158)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5152);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5176 =
              let uu____5177 = FStar_Syntax_Subst.compress head2  in
              uu____5177.FStar_Syntax_Syntax.n  in
            match uu____5176 with
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
                  (let uu____5183 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5183)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5186 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5186 with
                 | ((uu____5196,ty),uu____5198) ->
                     let uu____5203 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5203
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5216 =
                         let uu____5217 = FStar_Syntax_Subst.compress res  in
                         uu____5217.FStar_Syntax_Syntax.n  in
                       (match uu____5216 with
                        | FStar_Syntax_Syntax.Tm_app uu____5221 -> true
                        | uu____5239 ->
                            ((let uu____5241 =
                                let uu____5247 =
                                  let uu____5249 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5249
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5247)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5241);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5257 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5259 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5262) ->
                is_valid_application t2
            | uu____5267 -> false  in
          let uu____5269 = is_valid_application head1  in
          if uu____5269
          then
            let uu____5272 =
              let uu____5273 =
                let uu____5290 =
                  FStar_List.map
                    (fun uu____5319  ->
                       match uu____5319 with
                       | (t2,qual) ->
                           let uu____5344 = star_type' env t2  in
                           (uu____5344, qual)) args
                   in
                (head1, uu____5290)  in
              FStar_Syntax_Syntax.Tm_app uu____5273  in
            mk1 uu____5272
          else
            (let uu____5361 =
               let uu____5367 =
                 let uu____5369 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5369
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5367)  in
             FStar_Errors.raise_err uu____5361)
      | FStar_Syntax_Syntax.Tm_bvar uu____5373 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5374 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5375 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5376 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5404 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5404 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___525_5412 = env  in
                 let uu____5413 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5413;
                   subst = (uu___525_5412.subst);
                   tc_const = (uu___525_5412.tc_const)
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
               ((let uu___540_5440 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___540_5440.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___540_5440.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5447 =
            let uu____5448 =
              let uu____5455 = star_type' env t2  in (uu____5455, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5448  in
          mk1 uu____5447
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5507 =
            let uu____5508 =
              let uu____5535 = star_type' env e  in
              let uu____5538 =
                let uu____5555 =
                  let uu____5564 = star_type' env t2  in
                  FStar_Util.Inl uu____5564  in
                (uu____5555, FStar_Pervasives_Native.None)  in
              (uu____5535, uu____5538, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5508  in
          mk1 uu____5507
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5652 =
            let uu____5653 =
              let uu____5680 = star_type' env e  in
              let uu____5683 =
                let uu____5700 =
                  let uu____5709 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5709  in
                (uu____5700, FStar_Pervasives_Native.None)  in
              (uu____5680, uu____5683, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5653  in
          mk1 uu____5652
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5750,(uu____5751,FStar_Pervasives_Native.Some uu____5752),uu____5753)
          ->
          let uu____5802 =
            let uu____5808 =
              let uu____5810 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5810
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5808)  in
          FStar_Errors.raise_err uu____5802
      | FStar_Syntax_Syntax.Tm_refine uu____5814 ->
          let uu____5821 =
            let uu____5827 =
              let uu____5829 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5829
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5827)  in
          FStar_Errors.raise_err uu____5821
      | FStar_Syntax_Syntax.Tm_uinst uu____5833 ->
          let uu____5840 =
            let uu____5846 =
              let uu____5848 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5848
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5846)  in
          FStar_Errors.raise_err uu____5840
      | FStar_Syntax_Syntax.Tm_quoted uu____5852 ->
          let uu____5859 =
            let uu____5865 =
              let uu____5867 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5867
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5865)  in
          FStar_Errors.raise_err uu____5859
      | FStar_Syntax_Syntax.Tm_constant uu____5871 ->
          let uu____5872 =
            let uu____5878 =
              let uu____5880 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5880
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5878)  in
          FStar_Errors.raise_err uu____5872
      | FStar_Syntax_Syntax.Tm_match uu____5884 ->
          let uu____5907 =
            let uu____5913 =
              let uu____5915 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5915
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5913)  in
          FStar_Errors.raise_err uu____5907
      | FStar_Syntax_Syntax.Tm_let uu____5919 ->
          let uu____5933 =
            let uu____5939 =
              let uu____5941 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5941
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5939)  in
          FStar_Errors.raise_err uu____5933
      | FStar_Syntax_Syntax.Tm_uvar uu____5945 ->
          let uu____5958 =
            let uu____5964 =
              let uu____5966 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5966
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5964)  in
          FStar_Errors.raise_err uu____5958
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5970 =
            let uu____5976 =
              let uu____5978 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5978
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5976)  in
          FStar_Errors.raise_err uu____5970
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5983 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5983
      | FStar_Syntax_Syntax.Tm_delayed uu____5986 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_6018  ->
    match uu___3_6018 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_6029  ->
                match uu___2_6029 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____6032 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____6042 =
      let uu____6043 = FStar_Syntax_Subst.compress t  in
      uu____6043.FStar_Syntax_Syntax.n  in
    match uu____6042 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____6075 =
            let uu____6076 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____6076  in
          is_C uu____6075  in
        if r
        then
          ((let uu____6100 =
              let uu____6102 =
                FStar_List.for_all
                  (fun uu____6113  ->
                     match uu____6113 with | (h,uu____6122) -> is_C h) args
                 in
              Prims.op_Negation uu____6102  in
            if uu____6100 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6135 =
              let uu____6137 =
                FStar_List.for_all
                  (fun uu____6149  ->
                     match uu____6149 with
                     | (h,uu____6158) ->
                         let uu____6163 = is_C h  in
                         Prims.op_Negation uu____6163) args
                 in
              Prims.op_Negation uu____6137  in
            if uu____6135 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6192 = nm_of_comp comp  in
        (match uu____6192 with
         | M t1 ->
             ((let uu____6196 = is_C t1  in
               if uu____6196 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6205) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6211) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6217,uu____6218) -> is_C t1
    | uu____6259 -> false
  
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
          let uu____6295 =
            let uu____6296 =
              let uu____6313 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6316 =
                let uu____6327 =
                  let uu____6336 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6336)  in
                [uu____6327]  in
              (uu____6313, uu____6316)  in
            FStar_Syntax_Syntax.Tm_app uu____6296  in
          mk1 uu____6295  in
        let uu____6372 =
          let uu____6373 = FStar_Syntax_Syntax.mk_binder p  in [uu____6373]
           in
        FStar_Syntax_Util.abs uu____6372 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6398  ->
    match uu___4_6398 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6401 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6639 =
          match uu____6639 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6676 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6679 =
                       let uu____6681 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6681  in
                     Prims.op_Negation uu____6679)
                   in
                if uu____6676
                then
                  let uu____6683 =
                    let uu____6689 =
                      let uu____6691 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6693 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6695 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6691 uu____6693 uu____6695
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6689)  in
                  FStar_Errors.raise_err uu____6683
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6720 = mk_return env t1 s_e  in
                     ((M t1), uu____6720, u_e)))
               | (M t1,N t2) ->
                   let uu____6727 =
                     let uu____6733 =
                       let uu____6735 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6737 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6739 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6735 uu____6737 uu____6739
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6733)
                      in
                   FStar_Errors.raise_err uu____6727)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_6791 =
            match uu___5_6791 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6807 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6828 =
                let uu____6834 =
                  let uu____6836 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6836
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6834)  in
              FStar_Errors.raise_error uu____6828 e2.FStar_Syntax_Syntax.pos
          | M uu____6846 ->
              let uu____6847 = check env1 e2 context_nm  in
              strip_m uu____6847
           in
        let uu____6854 =
          let uu____6855 = FStar_Syntax_Subst.compress e  in
          uu____6855.FStar_Syntax_Syntax.n  in
        match uu____6854 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6864 ->
            let uu____6865 = infer env e  in return_if uu____6865
        | FStar_Syntax_Syntax.Tm_name uu____6872 ->
            let uu____6873 = infer env e  in return_if uu____6873
        | FStar_Syntax_Syntax.Tm_fvar uu____6880 ->
            let uu____6881 = infer env e  in return_if uu____6881
        | FStar_Syntax_Syntax.Tm_abs uu____6888 ->
            let uu____6907 = infer env e  in return_if uu____6907
        | FStar_Syntax_Syntax.Tm_constant uu____6914 ->
            let uu____6915 = infer env e  in return_if uu____6915
        | FStar_Syntax_Syntax.Tm_quoted uu____6922 ->
            let uu____6929 = infer env e  in return_if uu____6929
        | FStar_Syntax_Syntax.Tm_app uu____6936 ->
            let uu____6953 = infer env e  in return_if uu____6953
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6961 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6961 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____7026) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7032) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7038,uu____7039) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____7080 ->
            let uu____7094 =
              let uu____7096 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7096  in
            failwith uu____7094
        | FStar_Syntax_Syntax.Tm_type uu____7105 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7113 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7135 ->
            let uu____7142 =
              let uu____7144 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7144  in
            failwith uu____7142
        | FStar_Syntax_Syntax.Tm_uvar uu____7153 ->
            let uu____7166 =
              let uu____7168 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7168  in
            failwith uu____7166
        | FStar_Syntax_Syntax.Tm_delayed uu____7177 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7207 =
              let uu____7209 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7209  in
            failwith uu____7207

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
      let uu____7239 =
        let uu____7240 = FStar_Syntax_Subst.compress e  in
        uu____7240.FStar_Syntax_Syntax.n  in
      match uu____7239 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7259 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7259
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7310;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7311;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7317 =
                  let uu___775_7318 = rc  in
                  let uu____7319 =
                    let uu____7324 =
                      let uu____7327 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7327  in
                    FStar_Pervasives_Native.Some uu____7324  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___775_7318.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7319;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___775_7318.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7317
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___781_7339 = env  in
            let uu____7340 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7340;
              subst = (uu___781_7339.subst);
              tc_const = (uu___781_7339.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7366  ->
                 match uu____7366 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___788_7389 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___788_7389.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___788_7389.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7390 =
            FStar_List.fold_left
              (fun uu____7421  ->
                 fun uu____7422  ->
                   match (uu____7421, uu____7422) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7480 = is_C c  in
                       if uu____7480
                       then
                         let xw =
                           let uu____7490 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7490
                            in
                         let x =
                           let uu___800_7493 = bv  in
                           let uu____7494 =
                             let uu____7497 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7497  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___800_7493.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___800_7493.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7494
                           }  in
                         let env3 =
                           let uu___803_7499 = env2  in
                           let uu____7500 =
                             let uu____7503 =
                               let uu____7504 =
                                 let uu____7511 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7511)  in
                               FStar_Syntax_Syntax.NT uu____7504  in
                             uu____7503 :: (env2.subst)  in
                           {
                             tcenv = (uu___803_7499.tcenv);
                             subst = uu____7500;
                             tc_const = (uu___803_7499.tc_const)
                           }  in
                         let uu____7516 =
                           let uu____7519 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7520 =
                             let uu____7523 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7523 :: acc  in
                           uu____7519 :: uu____7520  in
                         (env3, uu____7516)
                       else
                         (let x =
                            let uu___806_7529 = bv  in
                            let uu____7530 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___806_7529.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___806_7529.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7530
                            }  in
                          let uu____7533 =
                            let uu____7536 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7536 :: acc  in
                          (env2, uu____7533))) (env1, []) binders1
             in
          (match uu____7390 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7556 =
                 let check_what =
                   let uu____7582 = is_monadic rc_opt1  in
                   if uu____7582 then check_m else check_n  in
                 let uu____7599 = check_what env2 body1  in
                 match uu____7599 with
                 | (t,s_body,u_body) ->
                     let uu____7619 =
                       let uu____7622 =
                         let uu____7623 = is_monadic rc_opt1  in
                         if uu____7623 then M t else N t  in
                       comp_of_nm uu____7622  in
                     (uu____7619, s_body, u_body)
                  in
               (match uu____7556 with
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
                                 let uu____7663 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7669  ->
                                           match uu___6_7669 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7672 -> false))
                                    in
                                 if uu____7663
                                 then
                                   let uu____7675 =
                                     FStar_List.filter
                                       (fun uu___7_7679  ->
                                          match uu___7_7679 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7682 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7675
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7693 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7699  ->
                                         match uu___8_7699 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7702 -> false))
                                  in
                               if uu____7693
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7711  ->
                                        match uu___9_7711 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7714 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7716 =
                                   let uu____7717 =
                                     let uu____7722 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7722
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7717 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7716
                               else
                                 (let uu____7729 =
                                    let uu___847_7730 = rc  in
                                    let uu____7731 =
                                      let uu____7736 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7736
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___847_7730.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7731;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___847_7730.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7729))
                       in
                    let uu____7741 =
                      let comp1 =
                        let uu____7749 = is_monadic rc_opt1  in
                        let uu____7751 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7749 uu____7751
                         in
                      let uu____7752 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7752,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7741 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7790 =
                             let uu____7791 =
                               let uu____7810 =
                                 let uu____7813 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7813 s_rc_opt  in
                               (s_binders1, s_body1, uu____7810)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7791  in
                           mk1 uu____7790  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7833 =
                             let uu____7834 =
                               let uu____7853 =
                                 let uu____7856 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7856 u_rc_opt  in
                               (u_binders2, u_body2, uu____7853)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7834  in
                           mk1 uu____7833  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7872;_};
            FStar_Syntax_Syntax.fv_delta = uu____7873;
            FStar_Syntax_Syntax.fv_qual = uu____7874;_}
          ->
          let uu____7877 =
            let uu____7882 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7882  in
          (match uu____7877 with
           | (uu____7913,t) ->
               let uu____7915 =
                 let uu____7916 = normalize1 t  in N uu____7916  in
               (uu____7915, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7917;
             FStar_Syntax_Syntax.vars = uu____7918;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7997 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7997 with
           | (unary_op1,uu____8021) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8092;
             FStar_Syntax_Syntax.vars = uu____8093;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8189 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8189 with
           | (unary_op1,uu____8213) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8292;
             FStar_Syntax_Syntax.vars = uu____8293;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8331 = infer env a  in
          (match uu____8331 with
           | (t,s,u) ->
               let uu____8347 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8347 with
                | (head1,uu____8371) ->
                    let uu____8396 =
                      let uu____8397 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8397  in
                    let uu____8398 =
                      let uu____8399 =
                        let uu____8400 =
                          let uu____8417 =
                            let uu____8428 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8428]  in
                          (head1, uu____8417)  in
                        FStar_Syntax_Syntax.Tm_app uu____8400  in
                      mk1 uu____8399  in
                    let uu____8465 =
                      let uu____8466 =
                        let uu____8467 =
                          let uu____8484 =
                            let uu____8495 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8495]  in
                          (head1, uu____8484)  in
                        FStar_Syntax_Syntax.Tm_app uu____8467  in
                      mk1 uu____8466  in
                    (uu____8396, uu____8398, uu____8465)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8532;
             FStar_Syntax_Syntax.vars = uu____8533;_},(a1,uu____8535)::a2::[])
          ->
          let uu____8591 = infer env a1  in
          (match uu____8591 with
           | (t,s,u) ->
               let uu____8607 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8607 with
                | (head1,uu____8631) ->
                    let uu____8656 =
                      let uu____8657 =
                        let uu____8658 =
                          let uu____8675 =
                            let uu____8686 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8686; a2]  in
                          (head1, uu____8675)  in
                        FStar_Syntax_Syntax.Tm_app uu____8658  in
                      mk1 uu____8657  in
                    let uu____8731 =
                      let uu____8732 =
                        let uu____8733 =
                          let uu____8750 =
                            let uu____8761 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8761; a2]  in
                          (head1, uu____8750)  in
                        FStar_Syntax_Syntax.Tm_app uu____8733  in
                      mk1 uu____8732  in
                    (t, uu____8656, uu____8731)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8806;
             FStar_Syntax_Syntax.vars = uu____8807;_},uu____8808)
          ->
          let uu____8833 =
            let uu____8839 =
              let uu____8841 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8841
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8839)  in
          FStar_Errors.raise_error uu____8833 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8851;
             FStar_Syntax_Syntax.vars = uu____8852;_},uu____8853)
          ->
          let uu____8878 =
            let uu____8884 =
              let uu____8886 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8886
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8884)  in
          FStar_Errors.raise_error uu____8878 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8922 = check_n env head1  in
          (match uu____8922 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8945 =
                   let uu____8946 = FStar_Syntax_Subst.compress t  in
                   uu____8946.FStar_Syntax_Syntax.n  in
                 match uu____8945 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8950 -> true
                 | uu____8966 -> false  in
               let rec flatten1 t =
                 let uu____8988 =
                   let uu____8989 = FStar_Syntax_Subst.compress t  in
                   uu____8989.FStar_Syntax_Syntax.n  in
                 match uu____8988 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____9008);
                                FStar_Syntax_Syntax.pos = uu____9009;
                                FStar_Syntax_Syntax.vars = uu____9010;_})
                     when is_arrow t1 ->
                     let uu____9039 = flatten1 t1  in
                     (match uu____9039 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9139,uu____9140)
                     -> flatten1 e1
                 | uu____9181 ->
                     let uu____9182 =
                       let uu____9188 =
                         let uu____9190 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9190
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9188)  in
                     FStar_Errors.raise_err uu____9182
                  in
               let uu____9208 = flatten1 t_head  in
               (match uu____9208 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9283 =
                          let uu____9289 =
                            let uu____9291 = FStar_Util.string_of_int n1  in
                            let uu____9293 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9295 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9291 uu____9293 uu____9295
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9289)
                           in
                        FStar_Errors.raise_err uu____9283)
                     else ();
                     (let uu____9301 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9301 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9354 args1 =
                            match uu____9354 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9454 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9454
                                 | (binders3,[]) ->
                                     let uu____9492 =
                                       let uu____9493 =
                                         let uu____9496 =
                                           let uu____9497 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9497
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9496
                                          in
                                       uu____9493.FStar_Syntax_Syntax.n  in
                                     (match uu____9492 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9530 =
                                            let uu____9531 =
                                              let uu____9532 =
                                                let uu____9547 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9547)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9532
                                               in
                                            mk1 uu____9531  in
                                          N uu____9530
                                      | uu____9560 -> failwith "wat?")
                                 | ([],uu____9562::uu____9563) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9616)::binders3,(arg,uu____9619)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9706 = FStar_List.splitAt n' binders1  in
                          (match uu____9706 with
                           | (binders2,uu____9740) ->
                               let uu____9773 =
                                 let uu____9796 =
                                   FStar_List.map2
                                     (fun uu____9858  ->
                                        fun uu____9859  ->
                                          match (uu____9858, uu____9859) with
                                          | ((bv,uu____9907),(arg,q)) ->
                                              let uu____9936 =
                                                let uu____9937 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9937.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9936 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9958 ->
                                                   let uu____9959 =
                                                     let uu____9966 =
                                                       star_type' env arg  in
                                                     (uu____9966, q)  in
                                                   (uu____9959, [(arg, q)])
                                               | uu____10003 ->
                                                   let uu____10004 =
                                                     check_n env arg  in
                                                   (match uu____10004 with
                                                    | (uu____10029,s_arg,u_arg)
                                                        ->
                                                        let uu____10032 =
                                                          let uu____10041 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____10041
                                                          then
                                                            let uu____10052 =
                                                              let uu____10059
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____10059,
                                                                q)
                                                               in
                                                            [uu____10052;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____10032))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9796  in
                               (match uu____9773 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10187 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10200 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10187, uu____10200)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10269) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10275) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10281,uu____10282) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10324 =
            let uu____10325 = env.tc_const c  in N uu____10325  in
          (uu____10324, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10332 ->
          let uu____10346 =
            let uu____10348 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10348  in
          failwith uu____10346
      | FStar_Syntax_Syntax.Tm_type uu____10357 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10365 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10387 ->
          let uu____10394 =
            let uu____10396 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10396  in
          failwith uu____10394
      | FStar_Syntax_Syntax.Tm_uvar uu____10405 ->
          let uu____10418 =
            let uu____10420 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10420  in
          failwith uu____10418
      | FStar_Syntax_Syntax.Tm_delayed uu____10429 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10459 =
            let uu____10461 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10461  in
          failwith uu____10459

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
          let uu____10510 = check_n env e0  in
          match uu____10510 with
          | (uu____10523,s_e0,u_e0) ->
              let uu____10526 =
                let uu____10555 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10616 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10616 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1122_10658 = env  in
                             let uu____10659 =
                               let uu____10660 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10660
                                in
                             {
                               tcenv = uu____10659;
                               subst = (uu___1122_10658.subst);
                               tc_const = (uu___1122_10658.tc_const)
                             }  in
                           let uu____10663 = f env1 body  in
                           (match uu____10663 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10735 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10555  in
              (match uu____10526 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10841 = FStar_List.hd nms  in
                     match uu____10841 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10850  ->
                          match uu___10_10850 with
                          | M uu____10852 -> true
                          | uu____10854 -> false) nms
                      in
                   let uu____10856 =
                     let uu____10893 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10983  ->
                              match uu____10983 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11167 =
                                         check env original_body (M t2)  in
                                       (match uu____11167 with
                                        | (uu____11204,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11243,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10893  in
                   (match uu____10856 with
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
                              (fun uu____11432  ->
                                 match uu____11432 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11483 =
                                         let uu____11484 =
                                           let uu____11501 =
                                             let uu____11512 =
                                               let uu____11521 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11524 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11521, uu____11524)  in
                                             [uu____11512]  in
                                           (s_body, uu____11501)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11484
                                          in
                                       mk1 uu____11483  in
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
                            let uu____11659 =
                              let uu____11660 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11660]  in
                            let uu____11679 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11659 uu____11679
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11703 =
                              let uu____11712 =
                                let uu____11719 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11719
                                 in
                              [uu____11712]  in
                            let uu____11738 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11703 uu____11738
                             in
                          let uu____11741 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11780 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11741, uu____11780)
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
                           let uu____11890 =
                             let uu____11891 =
                               let uu____11892 =
                                 let uu____11919 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11919,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11892
                                in
                             mk1 uu____11891  in
                           let uu____11978 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11890, uu____11978))))

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
              let uu____12043 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12043]  in
            let uu____12062 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12062 with
            | (x_binders1,e21) ->
                let uu____12075 = infer env e1  in
                (match uu____12075 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12092 = is_C t1  in
                       if uu____12092
                       then
                         let uu___1208_12095 = binding  in
                         let uu____12096 =
                           let uu____12099 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12099  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1208_12095.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1208_12095.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12096;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1208_12095.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1208_12095.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1208_12095.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1208_12095.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1211_12103 = env  in
                       let uu____12104 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1213_12106 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1213_12106.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1213_12106.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12104;
                         subst = (uu___1211_12103.subst);
                         tc_const = (uu___1211_12103.tc_const)
                       }  in
                     let uu____12107 = proceed env1 e21  in
                     (match uu____12107 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1220_12124 = binding  in
                            let uu____12125 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1220_12124.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1220_12124.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12125;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1220_12124.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1220_12124.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1220_12124.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1220_12124.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12128 =
                            let uu____12129 =
                              let uu____12130 =
                                let uu____12144 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1223_12161 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1223_12161.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1223_12161.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1223_12161.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1223_12161.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1223_12161.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1223_12161.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12144)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12130  in
                            mk1 uu____12129  in
                          let uu____12162 =
                            let uu____12163 =
                              let uu____12164 =
                                let uu____12178 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1225_12195 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1225_12195.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1225_12195.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1225_12195.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1225_12195.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1225_12195.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1225_12195.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12178)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12164  in
                            mk1 uu____12163  in
                          (nm_rec, uu____12128, uu____12162))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1232_12200 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1232_12200.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1232_12200.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1232_12200.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1232_12200.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1232_12200.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1235_12202 = env  in
                       let uu____12203 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1237_12205 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1237_12205.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1237_12205.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12203;
                         subst = (uu___1235_12202.subst);
                         tc_const = (uu___1235_12202.tc_const)
                       }  in
                     let uu____12206 = ensure_m env1 e21  in
                     (match uu____12206 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12230 =
                              let uu____12231 =
                                let uu____12248 =
                                  let uu____12259 =
                                    let uu____12268 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12271 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12268, uu____12271)  in
                                  [uu____12259]  in
                                (s_e2, uu____12248)  in
                              FStar_Syntax_Syntax.Tm_app uu____12231  in
                            mk1 uu____12230  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12313 =
                              let uu____12314 =
                                let uu____12331 =
                                  let uu____12342 =
                                    let uu____12351 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12351)  in
                                  [uu____12342]  in
                                (s_e1, uu____12331)  in
                              FStar_Syntax_Syntax.Tm_app uu____12314  in
                            mk1 uu____12313  in
                          let uu____12387 =
                            let uu____12388 =
                              let uu____12389 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12389]  in
                            FStar_Syntax_Util.abs uu____12388 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12408 =
                            let uu____12409 =
                              let uu____12410 =
                                let uu____12424 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1249_12441 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1249_12441.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1249_12441.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1249_12441.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1249_12441.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1249_12441.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1249_12441.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12424)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12410  in
                            mk1 uu____12409  in
                          ((M t2), uu____12387, uu____12408)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12451 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12451  in
      let uu____12452 = check env e mn  in
      match uu____12452 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12468 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12491 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12491  in
      let uu____12492 = check env e mn  in
      match uu____12492 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12508 -> failwith "[check_m]: impossible"

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
        (let uu____12541 =
           let uu____12543 = is_C c  in Prims.op_Negation uu____12543  in
         if uu____12541 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12557 =
           let uu____12558 = FStar_Syntax_Subst.compress c  in
           uu____12558.FStar_Syntax_Syntax.n  in
         match uu____12557 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12587 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12587 with
              | (wp_head,wp_args) ->
                  ((let uu____12631 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12650 =
                           let uu____12652 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12652
                            in
                         Prims.op_Negation uu____12650)
                       in
                    if uu____12631 then failwith "mismatch" else ());
                   (let uu____12665 =
                      let uu____12666 =
                        let uu____12683 =
                          FStar_List.map2
                            (fun uu____12721  ->
                               fun uu____12722  ->
                                 match (uu____12721, uu____12722) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12784 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12784
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12793 =
                                         let uu____12795 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12795 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12793
                                       then
                                         let uu____12797 =
                                           let uu____12803 =
                                             let uu____12805 =
                                               print_implicit q  in
                                             let uu____12807 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12805 uu____12807
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12803)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12797
                                       else ());
                                      (let uu____12813 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12813, q)))) args wp_args
                           in
                        (head1, uu____12683)  in
                      FStar_Syntax_Syntax.Tm_app uu____12666  in
                    mk1 uu____12665)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12859 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12859 with
              | (binders_orig,comp1) ->
                  let uu____12866 =
                    let uu____12883 =
                      FStar_List.map
                        (fun uu____12923  ->
                           match uu____12923 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12951 = is_C h  in
                               if uu____12951
                               then
                                 let w' =
                                   let uu____12967 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12967
                                    in
                                 let uu____12969 =
                                   let uu____12978 =
                                     let uu____12987 =
                                       let uu____12994 =
                                         let uu____12995 =
                                           let uu____12996 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12996  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12995
                                          in
                                       (uu____12994, q)  in
                                     [uu____12987]  in
                                   (w', q) :: uu____12978  in
                                 (w', uu____12969)
                               else
                                 (let x =
                                    let uu____13030 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13030
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12883  in
                  (match uu____12866 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13104 =
                           let uu____13107 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13107
                            in
                         FStar_Syntax_Subst.subst_comp uu____13104 comp1  in
                       let app =
                         let uu____13111 =
                           let uu____13112 =
                             let uu____13129 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13148 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13149 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13148, uu____13149)) bvs
                                in
                             (wp, uu____13129)  in
                           FStar_Syntax_Syntax.Tm_app uu____13112  in
                         mk1 uu____13111  in
                       let comp3 =
                         let uu____13164 = type_of_comp comp2  in
                         let uu____13165 = is_monadic_comp comp2  in
                         trans_G env uu____13164 uu____13165 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13168,uu____13169) ->
             trans_F_ env e wp
         | uu____13210 -> failwith "impossible trans_F_")

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
            let uu____13218 =
              let uu____13219 = star_type' env h  in
              let uu____13222 =
                let uu____13233 =
                  let uu____13242 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13242)  in
                [uu____13233]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13219;
                FStar_Syntax_Syntax.effect_args = uu____13222;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13218
          else
            (let uu____13268 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13268)

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
    fun t  -> let uu____13289 = n env.tcenv t  in star_type' env uu____13289
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13309 = n env.tcenv t  in check_n env uu____13309
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13326 = n env.tcenv c  in
        let uu____13327 = n env.tcenv wp  in
        trans_F_ env uu____13326 uu____13327
  