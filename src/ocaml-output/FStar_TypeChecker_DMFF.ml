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
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2048
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2047  in
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
                                   (Prims.parse_int "1"))
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
                    let uu____3967 =
                      let uu____3968 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____3968  in
                    let uu____3994 =
                      let uu___335_3995 = ed  in
                      let uu____3996 =
                        let uu____3997 = c wp_if_then_else2  in
                        ([], uu____3997)  in
                      let uu____4004 =
                        let uu____4005 = c ite_wp2  in ([], uu____4005)  in
                      let uu____4012 =
                        let uu____4013 = c stronger2  in ([], uu____4013)  in
                      let uu____4020 =
                        let uu____4021 = c wp_close2  in ([], uu____4021)  in
                      let uu____4028 =
                        let uu____4029 = c null_wp2  in ([], uu____4029)  in
                      let uu____4036 =
                        let uu____4037 = c wp_trivial2  in ([], uu____4037)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___335_3995.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___335_3995.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___335_3995.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___335_3995.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___335_3995.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___335_3995.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___335_3995.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3996;
                        FStar_Syntax_Syntax.ite_wp = uu____4004;
                        FStar_Syntax_Syntax.stronger = uu____4012;
                        FStar_Syntax_Syntax.close_wp = uu____4020;
                        FStar_Syntax_Syntax.null_wp = uu____4028;
                        FStar_Syntax_Syntax.trivial = uu____4036;
                        FStar_Syntax_Syntax.repr =
                          (uu___335_3995.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___335_3995.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___335_3995.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___335_3995.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___335_3995.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____3967, uu____3994)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___340_4061 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___340_4061.subst);
        tc_const = (uu___340_4061.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4082 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4101 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4121) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4135  ->
                match uu___0_4135 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4138 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4140 ->
        let uu____4141 =
          let uu____4147 =
            let uu____4149 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4149
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4147)  in
        FStar_Errors.raise_error uu____4141 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4159  ->
    match uu___1_4159 with
    | N t ->
        let uu____4162 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4162
    | M t ->
        let uu____4166 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4166
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4175,c) -> nm_of_comp c
    | uu____4197 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4210 = nm_of_comp c  in
    match uu____4210 with | M uu____4212 -> true | N uu____4214 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4225 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4241 =
        let uu____4250 =
          let uu____4257 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4257  in
        [uu____4250]  in
      let uu____4276 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4241 uu____4276  in
    let uu____4279 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4279
  
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
        let uu____4321 =
          let uu____4322 =
            let uu____4337 =
              let uu____4346 =
                let uu____4353 =
                  let uu____4354 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4354  in
                let uu____4355 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4353, uu____4355)  in
              [uu____4346]  in
            let uu____4373 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4337, uu____4373)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4322  in
        mk1 uu____4321

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4413) ->
          let binders1 =
            FStar_List.map
              (fun uu____4459  ->
                 match uu____4459 with
                 | (bv,aqual) ->
                     let uu____4478 =
                       let uu___390_4479 = bv  in
                       let uu____4480 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___390_4479.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___390_4479.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4480
                       }  in
                     (uu____4478, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4485,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4487);
                             FStar_Syntax_Syntax.pos = uu____4488;
                             FStar_Syntax_Syntax.vars = uu____4489;_})
               ->
               let uu____4518 =
                 let uu____4519 =
                   let uu____4534 =
                     let uu____4537 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4537  in
                   (binders1, uu____4534)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4519  in
               mk1 uu____4518
           | uu____4548 ->
               let uu____4549 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4549 with
                | N hn ->
                    let uu____4551 =
                      let uu____4552 =
                        let uu____4567 =
                          let uu____4570 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4570  in
                        (binders1, uu____4567)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4552  in
                    mk1 uu____4551
                | M a ->
                    let uu____4582 =
                      let uu____4583 =
                        let uu____4598 =
                          let uu____4607 =
                            let uu____4616 =
                              let uu____4623 =
                                let uu____4624 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4624  in
                              let uu____4625 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4623, uu____4625)  in
                            [uu____4616]  in
                          FStar_List.append binders1 uu____4607  in
                        let uu____4649 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4598, uu____4649)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4583  in
                    mk1 uu____4582))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4743 = f x  in
                    FStar_Util.string_builder_append strb uu____4743);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4752 = f x1  in
                         FStar_Util.string_builder_append strb uu____4752))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4756 =
              let uu____4762 =
                let uu____4764 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4766 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4764 uu____4766
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4762)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4756  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4788 =
              let uu____4789 = FStar_Syntax_Subst.compress ty  in
              uu____4789.FStar_Syntax_Syntax.n  in
            match uu____4788 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4815 =
                  let uu____4817 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4817  in
                if uu____4815
                then false
                else
                  (try
                     (fun uu___439_4834  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4858 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4858 s  in
                              let uu____4861 =
                                let uu____4863 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4863  in
                              if uu____4861
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4869 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4869 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4894  ->
                                          match uu____4894 with
                                          | (bv,uu____4906) ->
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
            | uu____4934 ->
                ((let uu____4936 =
                    let uu____4942 =
                      let uu____4944 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4944
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4942)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4936);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4960 =
              let uu____4961 = FStar_Syntax_Subst.compress head2  in
              uu____4961.FStar_Syntax_Syntax.n  in
            match uu____4960 with
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
                  (let uu____4967 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4967)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4970 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4970 with
                 | ((uu____4980,ty),uu____4982) ->
                     let uu____4987 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4987
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5000 =
                         let uu____5001 = FStar_Syntax_Subst.compress res  in
                         uu____5001.FStar_Syntax_Syntax.n  in
                       (match uu____5000 with
                        | FStar_Syntax_Syntax.Tm_app uu____5005 -> true
                        | uu____5023 ->
                            ((let uu____5025 =
                                let uu____5031 =
                                  let uu____5033 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5033
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5031)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5025);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5041 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5043 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5046) ->
                is_valid_application t2
            | uu____5051 -> false  in
          let uu____5053 = is_valid_application head1  in
          if uu____5053
          then
            let uu____5056 =
              let uu____5057 =
                let uu____5074 =
                  FStar_List.map
                    (fun uu____5103  ->
                       match uu____5103 with
                       | (t2,qual) ->
                           let uu____5128 = star_type' env t2  in
                           (uu____5128, qual)) args
                   in
                (head1, uu____5074)  in
              FStar_Syntax_Syntax.Tm_app uu____5057  in
            mk1 uu____5056
          else
            (let uu____5145 =
               let uu____5151 =
                 let uu____5153 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5153
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5151)  in
             FStar_Errors.raise_err uu____5145)
      | FStar_Syntax_Syntax.Tm_bvar uu____5157 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5158 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5159 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5160 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5188 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5188 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___511_5196 = env  in
                 let uu____5197 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5197;
                   subst = (uu___511_5196.subst);
                   tc_const = (uu___511_5196.tc_const)
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
               ((let uu___526_5224 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___526_5224.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___526_5224.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5231 =
            let uu____5232 =
              let uu____5239 = star_type' env t2  in (uu____5239, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5232  in
          mk1 uu____5231
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5291 =
            let uu____5292 =
              let uu____5319 = star_type' env e  in
              let uu____5322 =
                let uu____5339 =
                  let uu____5348 = star_type' env t2  in
                  FStar_Util.Inl uu____5348  in
                (uu____5339, FStar_Pervasives_Native.None)  in
              (uu____5319, uu____5322, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5292  in
          mk1 uu____5291
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5436 =
            let uu____5437 =
              let uu____5464 = star_type' env e  in
              let uu____5467 =
                let uu____5484 =
                  let uu____5493 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5493  in
                (uu____5484, FStar_Pervasives_Native.None)  in
              (uu____5464, uu____5467, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5437  in
          mk1 uu____5436
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5534,(uu____5535,FStar_Pervasives_Native.Some uu____5536),uu____5537)
          ->
          let uu____5586 =
            let uu____5592 =
              let uu____5594 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5594
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5592)  in
          FStar_Errors.raise_err uu____5586
      | FStar_Syntax_Syntax.Tm_refine uu____5598 ->
          let uu____5605 =
            let uu____5611 =
              let uu____5613 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5613
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5611)  in
          FStar_Errors.raise_err uu____5605
      | FStar_Syntax_Syntax.Tm_uinst uu____5617 ->
          let uu____5624 =
            let uu____5630 =
              let uu____5632 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5632
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5630)  in
          FStar_Errors.raise_err uu____5624
      | FStar_Syntax_Syntax.Tm_quoted uu____5636 ->
          let uu____5643 =
            let uu____5649 =
              let uu____5651 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5651
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5649)  in
          FStar_Errors.raise_err uu____5643
      | FStar_Syntax_Syntax.Tm_constant uu____5655 ->
          let uu____5656 =
            let uu____5662 =
              let uu____5664 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5664
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5662)  in
          FStar_Errors.raise_err uu____5656
      | FStar_Syntax_Syntax.Tm_match uu____5668 ->
          let uu____5691 =
            let uu____5697 =
              let uu____5699 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5699
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5697)  in
          FStar_Errors.raise_err uu____5691
      | FStar_Syntax_Syntax.Tm_let uu____5703 ->
          let uu____5717 =
            let uu____5723 =
              let uu____5725 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5725
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5723)  in
          FStar_Errors.raise_err uu____5717
      | FStar_Syntax_Syntax.Tm_uvar uu____5729 ->
          let uu____5742 =
            let uu____5748 =
              let uu____5750 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5750
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5748)  in
          FStar_Errors.raise_err uu____5742
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5754 =
            let uu____5760 =
              let uu____5762 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5762
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5760)  in
          FStar_Errors.raise_err uu____5754
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5767 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5767
      | FStar_Syntax_Syntax.Tm_delayed uu____5770 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_5802  ->
    match uu___3_5802 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_5813  ->
                match uu___2_5813 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5816 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5826 =
      let uu____5827 = FStar_Syntax_Subst.compress t  in
      uu____5827.FStar_Syntax_Syntax.n  in
    match uu____5826 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5859 =
            let uu____5860 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5860  in
          is_C uu____5859  in
        if r
        then
          ((let uu____5884 =
              let uu____5886 =
                FStar_List.for_all
                  (fun uu____5897  ->
                     match uu____5897 with | (h,uu____5906) -> is_C h) args
                 in
              Prims.op_Negation uu____5886  in
            if uu____5884 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5919 =
              let uu____5921 =
                FStar_List.for_all
                  (fun uu____5933  ->
                     match uu____5933 with
                     | (h,uu____5942) ->
                         let uu____5947 = is_C h  in
                         Prims.op_Negation uu____5947) args
                 in
              Prims.op_Negation uu____5921  in
            if uu____5919 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5976 = nm_of_comp comp  in
        (match uu____5976 with
         | M t1 ->
             ((let uu____5980 = is_C t1  in
               if uu____5980 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5989) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5995) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6001,uu____6002) -> is_C t1
    | uu____6043 -> false
  
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
          let uu____6079 =
            let uu____6080 =
              let uu____6097 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6100 =
                let uu____6111 =
                  let uu____6120 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6120)  in
                [uu____6111]  in
              (uu____6097, uu____6100)  in
            FStar_Syntax_Syntax.Tm_app uu____6080  in
          mk1 uu____6079  in
        let uu____6156 =
          let uu____6157 = FStar_Syntax_Syntax.mk_binder p  in [uu____6157]
           in
        FStar_Syntax_Util.abs uu____6156 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6182  ->
    match uu___4_6182 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6185 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6423 =
          match uu____6423 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6460 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6463 =
                       let uu____6465 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6465  in
                     Prims.op_Negation uu____6463)
                   in
                if uu____6460
                then
                  let uu____6467 =
                    let uu____6473 =
                      let uu____6475 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6477 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6479 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6475 uu____6477 uu____6479
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6473)  in
                  FStar_Errors.raise_err uu____6467
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6504 = mk_return env t1 s_e  in
                     ((M t1), uu____6504, u_e)))
               | (M t1,N t2) ->
                   let uu____6511 =
                     let uu____6517 =
                       let uu____6519 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6521 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6523 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6519 uu____6521 uu____6523
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6517)
                      in
                   FStar_Errors.raise_err uu____6511)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_6575 =
            match uu___5_6575 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6591 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6612 =
                let uu____6618 =
                  let uu____6620 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6620
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6618)  in
              FStar_Errors.raise_error uu____6612 e2.FStar_Syntax_Syntax.pos
          | M uu____6630 ->
              let uu____6631 = check env1 e2 context_nm  in
              strip_m uu____6631
           in
        let uu____6638 =
          let uu____6639 = FStar_Syntax_Subst.compress e  in
          uu____6639.FStar_Syntax_Syntax.n  in
        match uu____6638 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6648 ->
            let uu____6649 = infer env e  in return_if uu____6649
        | FStar_Syntax_Syntax.Tm_name uu____6656 ->
            let uu____6657 = infer env e  in return_if uu____6657
        | FStar_Syntax_Syntax.Tm_fvar uu____6664 ->
            let uu____6665 = infer env e  in return_if uu____6665
        | FStar_Syntax_Syntax.Tm_abs uu____6672 ->
            let uu____6691 = infer env e  in return_if uu____6691
        | FStar_Syntax_Syntax.Tm_constant uu____6698 ->
            let uu____6699 = infer env e  in return_if uu____6699
        | FStar_Syntax_Syntax.Tm_quoted uu____6706 ->
            let uu____6713 = infer env e  in return_if uu____6713
        | FStar_Syntax_Syntax.Tm_app uu____6720 ->
            let uu____6737 = infer env e  in return_if uu____6737
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6745 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6745 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6810) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6816) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6822,uu____6823) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6864 ->
            let uu____6878 =
              let uu____6880 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6880  in
            failwith uu____6878
        | FStar_Syntax_Syntax.Tm_type uu____6889 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6897 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6919 ->
            let uu____6926 =
              let uu____6928 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6928  in
            failwith uu____6926
        | FStar_Syntax_Syntax.Tm_uvar uu____6937 ->
            let uu____6950 =
              let uu____6952 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6952  in
            failwith uu____6950
        | FStar_Syntax_Syntax.Tm_delayed uu____6961 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6991 =
              let uu____6993 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6993  in
            failwith uu____6991

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
      let uu____7023 =
        let uu____7024 = FStar_Syntax_Subst.compress e  in
        uu____7024.FStar_Syntax_Syntax.n  in
      match uu____7023 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7043 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7043
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7094;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7095;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7101 =
                  let uu___761_7102 = rc  in
                  let uu____7103 =
                    let uu____7108 =
                      let uu____7111 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7111  in
                    FStar_Pervasives_Native.Some uu____7108  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___761_7102.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7103;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___761_7102.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7101
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___767_7123 = env  in
            let uu____7124 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7124;
              subst = (uu___767_7123.subst);
              tc_const = (uu___767_7123.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7150  ->
                 match uu____7150 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___774_7173 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___774_7173.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___774_7173.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7174 =
            FStar_List.fold_left
              (fun uu____7205  ->
                 fun uu____7206  ->
                   match (uu____7205, uu____7206) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7264 = is_C c  in
                       if uu____7264
                       then
                         let xw =
                           let uu____7274 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7274
                            in
                         let x =
                           let uu___786_7277 = bv  in
                           let uu____7278 =
                             let uu____7281 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7281  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___786_7277.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___786_7277.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7278
                           }  in
                         let env3 =
                           let uu___789_7283 = env2  in
                           let uu____7284 =
                             let uu____7287 =
                               let uu____7288 =
                                 let uu____7295 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7295)  in
                               FStar_Syntax_Syntax.NT uu____7288  in
                             uu____7287 :: (env2.subst)  in
                           {
                             tcenv = (uu___789_7283.tcenv);
                             subst = uu____7284;
                             tc_const = (uu___789_7283.tc_const)
                           }  in
                         let uu____7300 =
                           let uu____7303 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7304 =
                             let uu____7307 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7307 :: acc  in
                           uu____7303 :: uu____7304  in
                         (env3, uu____7300)
                       else
                         (let x =
                            let uu___792_7313 = bv  in
                            let uu____7314 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___792_7313.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___792_7313.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7314
                            }  in
                          let uu____7317 =
                            let uu____7320 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7320 :: acc  in
                          (env2, uu____7317))) (env1, []) binders1
             in
          (match uu____7174 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7340 =
                 let check_what =
                   let uu____7366 = is_monadic rc_opt1  in
                   if uu____7366 then check_m else check_n  in
                 let uu____7383 = check_what env2 body1  in
                 match uu____7383 with
                 | (t,s_body,u_body) ->
                     let uu____7403 =
                       let uu____7406 =
                         let uu____7407 = is_monadic rc_opt1  in
                         if uu____7407 then M t else N t  in
                       comp_of_nm uu____7406  in
                     (uu____7403, s_body, u_body)
                  in
               (match uu____7340 with
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
                                 let uu____7447 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7453  ->
                                           match uu___6_7453 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7456 -> false))
                                    in
                                 if uu____7447
                                 then
                                   let uu____7459 =
                                     FStar_List.filter
                                       (fun uu___7_7463  ->
                                          match uu___7_7463 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7466 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7459
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7477 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7483  ->
                                         match uu___8_7483 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7486 -> false))
                                  in
                               if uu____7477
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7495  ->
                                        match uu___9_7495 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7498 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7500 =
                                   let uu____7501 =
                                     let uu____7506 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7506
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7501 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7500
                               else
                                 (let uu____7513 =
                                    let uu___833_7514 = rc  in
                                    let uu____7515 =
                                      let uu____7520 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7520
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___833_7514.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7515;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___833_7514.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7513))
                       in
                    let uu____7525 =
                      let comp1 =
                        let uu____7533 = is_monadic rc_opt1  in
                        let uu____7535 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7533 uu____7535
                         in
                      let uu____7536 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7536,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7525 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7574 =
                             let uu____7575 =
                               let uu____7594 =
                                 let uu____7597 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7597 s_rc_opt  in
                               (s_binders1, s_body1, uu____7594)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7575  in
                           mk1 uu____7574  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7617 =
                             let uu____7618 =
                               let uu____7637 =
                                 let uu____7640 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7640 u_rc_opt  in
                               (u_binders2, u_body2, uu____7637)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7618  in
                           mk1 uu____7617  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7656;_};
            FStar_Syntax_Syntax.fv_delta = uu____7657;
            FStar_Syntax_Syntax.fv_qual = uu____7658;_}
          ->
          let uu____7661 =
            let uu____7666 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7666  in
          (match uu____7661 with
           | (uu____7697,t) ->
               let uu____7699 =
                 let uu____7700 = normalize1 t  in N uu____7700  in
               (uu____7699, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7701;
             FStar_Syntax_Syntax.vars = uu____7702;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7781 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7781 with
           | (unary_op1,uu____7805) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7876;
             FStar_Syntax_Syntax.vars = uu____7877;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7973 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7973 with
           | (unary_op1,uu____7997) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8076;
             FStar_Syntax_Syntax.vars = uu____8077;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8115 = infer env a  in
          (match uu____8115 with
           | (t,s,u) ->
               let uu____8131 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8131 with
                | (head1,uu____8155) ->
                    let uu____8180 =
                      let uu____8181 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8181  in
                    let uu____8182 =
                      let uu____8183 =
                        let uu____8184 =
                          let uu____8201 =
                            let uu____8212 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8212]  in
                          (head1, uu____8201)  in
                        FStar_Syntax_Syntax.Tm_app uu____8184  in
                      mk1 uu____8183  in
                    let uu____8249 =
                      let uu____8250 =
                        let uu____8251 =
                          let uu____8268 =
                            let uu____8279 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8279]  in
                          (head1, uu____8268)  in
                        FStar_Syntax_Syntax.Tm_app uu____8251  in
                      mk1 uu____8250  in
                    (uu____8180, uu____8182, uu____8249)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8316;
             FStar_Syntax_Syntax.vars = uu____8317;_},(a1,uu____8319)::a2::[])
          ->
          let uu____8375 = infer env a1  in
          (match uu____8375 with
           | (t,s,u) ->
               let uu____8391 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8391 with
                | (head1,uu____8415) ->
                    let uu____8440 =
                      let uu____8441 =
                        let uu____8442 =
                          let uu____8459 =
                            let uu____8470 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8470; a2]  in
                          (head1, uu____8459)  in
                        FStar_Syntax_Syntax.Tm_app uu____8442  in
                      mk1 uu____8441  in
                    let uu____8515 =
                      let uu____8516 =
                        let uu____8517 =
                          let uu____8534 =
                            let uu____8545 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8545; a2]  in
                          (head1, uu____8534)  in
                        FStar_Syntax_Syntax.Tm_app uu____8517  in
                      mk1 uu____8516  in
                    (t, uu____8440, uu____8515)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8590;
             FStar_Syntax_Syntax.vars = uu____8591;_},uu____8592)
          ->
          let uu____8617 =
            let uu____8623 =
              let uu____8625 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8625
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8623)  in
          FStar_Errors.raise_error uu____8617 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8635;
             FStar_Syntax_Syntax.vars = uu____8636;_},uu____8637)
          ->
          let uu____8662 =
            let uu____8668 =
              let uu____8670 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8670
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8668)  in
          FStar_Errors.raise_error uu____8662 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8706 = check_n env head1  in
          (match uu____8706 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8729 =
                   let uu____8730 = FStar_Syntax_Subst.compress t  in
                   uu____8730.FStar_Syntax_Syntax.n  in
                 match uu____8729 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8734 -> true
                 | uu____8750 -> false  in
               let rec flatten1 t =
                 let uu____8772 =
                   let uu____8773 = FStar_Syntax_Subst.compress t  in
                   uu____8773.FStar_Syntax_Syntax.n  in
                 match uu____8772 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8792);
                                FStar_Syntax_Syntax.pos = uu____8793;
                                FStar_Syntax_Syntax.vars = uu____8794;_})
                     when is_arrow t1 ->
                     let uu____8823 = flatten1 t1  in
                     (match uu____8823 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8923,uu____8924)
                     -> flatten1 e1
                 | uu____8965 ->
                     let uu____8966 =
                       let uu____8972 =
                         let uu____8974 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____8974
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____8972)  in
                     FStar_Errors.raise_err uu____8966
                  in
               let uu____8992 = flatten1 t_head  in
               (match uu____8992 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9067 =
                          let uu____9073 =
                            let uu____9075 = FStar_Util.string_of_int n1  in
                            let uu____9077 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9079 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9075 uu____9077 uu____9079
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9073)
                           in
                        FStar_Errors.raise_err uu____9067)
                     else ();
                     (let uu____9085 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9085 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9138 args1 =
                            match uu____9138 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9238 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9238
                                 | (binders3,[]) ->
                                     let uu____9276 =
                                       let uu____9277 =
                                         let uu____9280 =
                                           let uu____9281 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9281
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9280
                                          in
                                       uu____9277.FStar_Syntax_Syntax.n  in
                                     (match uu____9276 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9314 =
                                            let uu____9315 =
                                              let uu____9316 =
                                                let uu____9331 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9331)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9316
                                               in
                                            mk1 uu____9315  in
                                          N uu____9314
                                      | uu____9344 -> failwith "wat?")
                                 | ([],uu____9346::uu____9347) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9400)::binders3,(arg,uu____9403)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9490 = FStar_List.splitAt n' binders1  in
                          (match uu____9490 with
                           | (binders2,uu____9524) ->
                               let uu____9557 =
                                 let uu____9580 =
                                   FStar_List.map2
                                     (fun uu____9642  ->
                                        fun uu____9643  ->
                                          match (uu____9642, uu____9643) with
                                          | ((bv,uu____9691),(arg,q)) ->
                                              let uu____9720 =
                                                let uu____9721 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9721.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9720 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9742 ->
                                                   let uu____9743 =
                                                     let uu____9750 =
                                                       star_type' env arg  in
                                                     (uu____9750, q)  in
                                                   (uu____9743, [(arg, q)])
                                               | uu____9787 ->
                                                   let uu____9788 =
                                                     check_n env arg  in
                                                   (match uu____9788 with
                                                    | (uu____9813,s_arg,u_arg)
                                                        ->
                                                        let uu____9816 =
                                                          let uu____9825 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9825
                                                          then
                                                            let uu____9836 =
                                                              let uu____9843
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9843, q)
                                                               in
                                                            [uu____9836;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9816))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9580  in
                               (match uu____9557 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____9971 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____9984 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____9971, uu____9984)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10053) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10059) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10065,uu____10066) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10108 =
            let uu____10109 = env.tc_const c  in N uu____10109  in
          (uu____10108, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10116 ->
          let uu____10130 =
            let uu____10132 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10132  in
          failwith uu____10130
      | FStar_Syntax_Syntax.Tm_type uu____10141 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10149 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10171 ->
          let uu____10178 =
            let uu____10180 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10180  in
          failwith uu____10178
      | FStar_Syntax_Syntax.Tm_uvar uu____10189 ->
          let uu____10202 =
            let uu____10204 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10204  in
          failwith uu____10202
      | FStar_Syntax_Syntax.Tm_delayed uu____10213 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10243 =
            let uu____10245 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10245  in
          failwith uu____10243

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
          let uu____10294 = check_n env e0  in
          match uu____10294 with
          | (uu____10307,s_e0,u_e0) ->
              let uu____10310 =
                let uu____10339 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10400 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10400 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1108_10442 = env  in
                             let uu____10443 =
                               let uu____10444 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10444
                                in
                             {
                               tcenv = uu____10443;
                               subst = (uu___1108_10442.subst);
                               tc_const = (uu___1108_10442.tc_const)
                             }  in
                           let uu____10447 = f env1 body  in
                           (match uu____10447 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10519 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10339  in
              (match uu____10310 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10625 = FStar_List.hd nms  in
                     match uu____10625 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10634  ->
                          match uu___10_10634 with
                          | M uu____10636 -> true
                          | uu____10638 -> false) nms
                      in
                   let uu____10640 =
                     let uu____10677 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10767  ->
                              match uu____10767 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____10951 =
                                         check env original_body (M t2)  in
                                       (match uu____10951 with
                                        | (uu____10988,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11027,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10677  in
                   (match uu____10640 with
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
                              (fun uu____11216  ->
                                 match uu____11216 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11267 =
                                         let uu____11268 =
                                           let uu____11285 =
                                             let uu____11296 =
                                               let uu____11305 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11308 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11305, uu____11308)  in
                                             [uu____11296]  in
                                           (s_body, uu____11285)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11268
                                          in
                                       mk1 uu____11267  in
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
                            let uu____11443 =
                              let uu____11444 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11444]  in
                            let uu____11463 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11443 uu____11463
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11487 =
                              let uu____11496 =
                                let uu____11503 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11503
                                 in
                              [uu____11496]  in
                            let uu____11522 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11487 uu____11522
                             in
                          let uu____11525 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11564 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11525, uu____11564)
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
                           let uu____11674 =
                             let uu____11675 =
                               let uu____11676 =
                                 let uu____11703 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11703,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11676
                                in
                             mk1 uu____11675  in
                           let uu____11762 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11674, uu____11762))))

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
              let uu____11827 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11827]  in
            let uu____11846 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11846 with
            | (x_binders1,e21) ->
                let uu____11859 = infer env e1  in
                (match uu____11859 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____11876 = is_C t1  in
                       if uu____11876
                       then
                         let uu___1194_11879 = binding  in
                         let uu____11880 =
                           let uu____11883 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____11883  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1194_11879.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1194_11879.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11880;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1194_11879.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1194_11879.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1194_11879.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1194_11879.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1197_11887 = env  in
                       let uu____11888 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1199_11890 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1199_11890.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1199_11890.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11888;
                         subst = (uu___1197_11887.subst);
                         tc_const = (uu___1197_11887.tc_const)
                       }  in
                     let uu____11891 = proceed env1 e21  in
                     (match uu____11891 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1206_11908 = binding  in
                            let uu____11909 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1206_11908.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1206_11908.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11909;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1206_11908.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1206_11908.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1206_11908.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1206_11908.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____11912 =
                            let uu____11913 =
                              let uu____11914 =
                                let uu____11928 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1209_11945 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1209_11945.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1209_11945.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1209_11945.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1209_11945.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1209_11945.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1209_11945.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11928)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11914  in
                            mk1 uu____11913  in
                          let uu____11946 =
                            let uu____11947 =
                              let uu____11948 =
                                let uu____11962 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1211_11979 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1211_11979.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1211_11979.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1211_11979.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1211_11979.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1211_11979.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1211_11979.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11962)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11948  in
                            mk1 uu____11947  in
                          (nm_rec, uu____11912, uu____11946))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1218_11984 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1218_11984.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1218_11984.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1218_11984.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1218_11984.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1218_11984.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1221_11986 = env  in
                       let uu____11987 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1223_11989 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1223_11989.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1223_11989.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11987;
                         subst = (uu___1221_11986.subst);
                         tc_const = (uu___1221_11986.tc_const)
                       }  in
                     let uu____11990 = ensure_m env1 e21  in
                     (match uu____11990 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12014 =
                              let uu____12015 =
                                let uu____12032 =
                                  let uu____12043 =
                                    let uu____12052 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12055 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12052, uu____12055)  in
                                  [uu____12043]  in
                                (s_e2, uu____12032)  in
                              FStar_Syntax_Syntax.Tm_app uu____12015  in
                            mk1 uu____12014  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12097 =
                              let uu____12098 =
                                let uu____12115 =
                                  let uu____12126 =
                                    let uu____12135 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12135)  in
                                  [uu____12126]  in
                                (s_e1, uu____12115)  in
                              FStar_Syntax_Syntax.Tm_app uu____12098  in
                            mk1 uu____12097  in
                          let uu____12171 =
                            let uu____12172 =
                              let uu____12173 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12173]  in
                            FStar_Syntax_Util.abs uu____12172 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12192 =
                            let uu____12193 =
                              let uu____12194 =
                                let uu____12208 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1235_12225 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1235_12225.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1235_12225.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1235_12225.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1235_12225.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1235_12225.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1235_12225.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12208)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12194  in
                            mk1 uu____12193  in
                          ((M t2), uu____12171, uu____12192)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12235 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12235  in
      let uu____12236 = check env e mn  in
      match uu____12236 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12252 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12275 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12275  in
      let uu____12276 = check env e mn  in
      match uu____12276 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12292 -> failwith "[check_m]: impossible"

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
        (let uu____12325 =
           let uu____12327 = is_C c  in Prims.op_Negation uu____12327  in
         if uu____12325 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12341 =
           let uu____12342 = FStar_Syntax_Subst.compress c  in
           uu____12342.FStar_Syntax_Syntax.n  in
         match uu____12341 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12371 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12371 with
              | (wp_head,wp_args) ->
                  ((let uu____12415 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12434 =
                           let uu____12436 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12436
                            in
                         Prims.op_Negation uu____12434)
                       in
                    if uu____12415 then failwith "mismatch" else ());
                   (let uu____12449 =
                      let uu____12450 =
                        let uu____12467 =
                          FStar_List.map2
                            (fun uu____12505  ->
                               fun uu____12506  ->
                                 match (uu____12505, uu____12506) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12568 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12568
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12577 =
                                         let uu____12579 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12579 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12577
                                       then
                                         let uu____12581 =
                                           let uu____12587 =
                                             let uu____12589 =
                                               print_implicit q  in
                                             let uu____12591 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12589 uu____12591
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12587)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12581
                                       else ());
                                      (let uu____12597 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12597, q)))) args wp_args
                           in
                        (head1, uu____12467)  in
                      FStar_Syntax_Syntax.Tm_app uu____12450  in
                    mk1 uu____12449)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12643 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12643 with
              | (binders_orig,comp1) ->
                  let uu____12650 =
                    let uu____12667 =
                      FStar_List.map
                        (fun uu____12707  ->
                           match uu____12707 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12735 = is_C h  in
                               if uu____12735
                               then
                                 let w' =
                                   let uu____12751 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12751
                                    in
                                 let uu____12753 =
                                   let uu____12762 =
                                     let uu____12771 =
                                       let uu____12778 =
                                         let uu____12779 =
                                           let uu____12780 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12780  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12779
                                          in
                                       (uu____12778, q)  in
                                     [uu____12771]  in
                                   (w', q) :: uu____12762  in
                                 (w', uu____12753)
                               else
                                 (let x =
                                    let uu____12814 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____12814
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12667  in
                  (match uu____12650 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____12888 =
                           let uu____12891 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12891
                            in
                         FStar_Syntax_Subst.subst_comp uu____12888 comp1  in
                       let app =
                         let uu____12895 =
                           let uu____12896 =
                             let uu____12913 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____12932 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____12933 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12932, uu____12933)) bvs
                                in
                             (wp, uu____12913)  in
                           FStar_Syntax_Syntax.Tm_app uu____12896  in
                         mk1 uu____12895  in
                       let comp3 =
                         let uu____12948 = type_of_comp comp2  in
                         let uu____12949 = is_monadic_comp comp2  in
                         trans_G env uu____12948 uu____12949 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____12952,uu____12953) ->
             trans_F_ env e wp
         | uu____12994 -> failwith "impossible trans_F_")

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
            let uu____13002 =
              let uu____13003 = star_type' env h  in
              let uu____13006 =
                let uu____13017 =
                  let uu____13026 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13026)  in
                [uu____13017]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13003;
                FStar_Syntax_Syntax.effect_args = uu____13006;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13002
          else
            (let uu____13052 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13052)

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
    fun t  -> let uu____13073 = n env.tcenv t  in star_type' env uu____13073
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13093 = n env.tcenv t  in check_n env uu____13093
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13110 = n env.tcenv c  in
        let uu____13111 = n env.tcenv wp  in
        trans_F_ env uu____13110 uu____13111
  