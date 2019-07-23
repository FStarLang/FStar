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
                    let uu____3967 =
                      let uu____3968 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____3968  in
                    let uu____3994 =
                      let uu___335_3995 = ed  in
                      let uu____3996 =
                        let uu____3997 = c stronger2  in ([], uu____3997)  in
                      let uu____4004 =
                        let uu____4009 =
                          let uu____4010 =
                            let uu____4011 = c wp_if_then_else2  in
                            ([], uu____4011)  in
                          let uu____4018 =
                            let uu____4019 = c ite_wp2  in ([], uu____4019)
                             in
                          let uu____4026 =
                            let uu____4027 = c wp_close2  in ([], uu____4027)
                             in
                          {
                            FStar_Syntax_Syntax.if_then_else = uu____4010;
                            FStar_Syntax_Syntax.ite_wp = uu____4018;
                            FStar_Syntax_Syntax.close_wp = uu____4026
                          }  in
                        FStar_Util.Inl uu____4009  in
                      let uu____4034 =
                        let uu____4037 =
                          let uu____4038 = c wp_trivial2  in ([], uu____4038)
                           in
                        FStar_Pervasives_Native.Some uu____4037  in
                      {
                        FStar_Syntax_Syntax.is_layered =
                          (uu___335_3995.FStar_Syntax_Syntax.is_layered);
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
                        FStar_Syntax_Syntax.stronger = uu____3996;
                        FStar_Syntax_Syntax.match_wps = uu____4004;
                        FStar_Syntax_Syntax.trivial = uu____4034;
                        FStar_Syntax_Syntax.repr =
                          (uu___335_3995.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___335_3995.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___335_3995.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.stronger_repr =
                          (uu___335_3995.FStar_Syntax_Syntax.stronger_repr);
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
      let uu___340_4062 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___340_4062.subst);
        tc_const = (uu___340_4062.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4083 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4102 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4122) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4136  ->
                match uu___0_4136 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4139 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4141 ->
        let uu____4142 =
          let uu____4148 =
            let uu____4150 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4150
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4148)  in
        FStar_Errors.raise_error uu____4142 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4160  ->
    match uu___1_4160 with
    | N t ->
        let uu____4163 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4163
    | M t ->
        let uu____4167 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4167
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4176,c) -> nm_of_comp c
    | uu____4198 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4211 = nm_of_comp c  in
    match uu____4211 with | M uu____4213 -> true | N uu____4215 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4226 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4242 =
        let uu____4251 =
          let uu____4258 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4258  in
        [uu____4251]  in
      let uu____4277 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4242 uu____4277  in
    let uu____4280 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4280
  
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
        let uu____4322 =
          let uu____4323 =
            let uu____4338 =
              let uu____4347 =
                let uu____4354 =
                  let uu____4355 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4355  in
                let uu____4356 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4354, uu____4356)  in
              [uu____4347]  in
            let uu____4374 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4338, uu____4374)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4323  in
        mk1 uu____4322

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4414) ->
          let binders1 =
            FStar_List.map
              (fun uu____4460  ->
                 match uu____4460 with
                 | (bv,aqual) ->
                     let uu____4479 =
                       let uu___390_4480 = bv  in
                       let uu____4481 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___390_4480.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___390_4480.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4481
                       }  in
                     (uu____4479, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4486,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4488);
                             FStar_Syntax_Syntax.pos = uu____4489;
                             FStar_Syntax_Syntax.vars = uu____4490;_})
               ->
               let uu____4519 =
                 let uu____4520 =
                   let uu____4535 =
                     let uu____4538 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4538  in
                   (binders1, uu____4535)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4520  in
               mk1 uu____4519
           | uu____4549 ->
               let uu____4550 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4550 with
                | N hn ->
                    let uu____4552 =
                      let uu____4553 =
                        let uu____4568 =
                          let uu____4571 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4571  in
                        (binders1, uu____4568)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4553  in
                    mk1 uu____4552
                | M a ->
                    let uu____4583 =
                      let uu____4584 =
                        let uu____4599 =
                          let uu____4608 =
                            let uu____4617 =
                              let uu____4624 =
                                let uu____4625 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4625  in
                              let uu____4626 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4624, uu____4626)  in
                            [uu____4617]  in
                          FStar_List.append binders1 uu____4608  in
                        let uu____4650 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4599, uu____4650)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4584  in
                    mk1 uu____4583))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4744 = f x  in
                    FStar_Util.string_builder_append strb uu____4744);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4753 = f x1  in
                         FStar_Util.string_builder_append strb uu____4753))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4757 =
              let uu____4763 =
                let uu____4765 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4767 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4765 uu____4767
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4763)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4757  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4789 =
              let uu____4790 = FStar_Syntax_Subst.compress ty  in
              uu____4790.FStar_Syntax_Syntax.n  in
            match uu____4789 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4816 =
                  let uu____4818 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4818  in
                if uu____4816
                then false
                else
                  (try
                     (fun uu___439_4835  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4859 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4859 s  in
                              let uu____4862 =
                                let uu____4864 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4864  in
                              if uu____4862
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4870 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4870 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4895  ->
                                          match uu____4895 with
                                          | (bv,uu____4907) ->
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
            | uu____4935 ->
                ((let uu____4937 =
                    let uu____4943 =
                      let uu____4945 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4945
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4943)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4937);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4961 =
              let uu____4962 = FStar_Syntax_Subst.compress head2  in
              uu____4962.FStar_Syntax_Syntax.n  in
            match uu____4961 with
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
                  (let uu____4968 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4968)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4971 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4971 with
                 | ((uu____4981,ty),uu____4983) ->
                     let uu____4988 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4988
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5001 =
                         let uu____5002 = FStar_Syntax_Subst.compress res  in
                         uu____5002.FStar_Syntax_Syntax.n  in
                       (match uu____5001 with
                        | FStar_Syntax_Syntax.Tm_app uu____5006 -> true
                        | uu____5024 ->
                            ((let uu____5026 =
                                let uu____5032 =
                                  let uu____5034 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5034
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5032)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5026);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5042 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5044 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5047) ->
                is_valid_application t2
            | uu____5052 -> false  in
          let uu____5054 = is_valid_application head1  in
          if uu____5054
          then
            let uu____5057 =
              let uu____5058 =
                let uu____5075 =
                  FStar_List.map
                    (fun uu____5104  ->
                       match uu____5104 with
                       | (t2,qual) ->
                           let uu____5129 = star_type' env t2  in
                           (uu____5129, qual)) args
                   in
                (head1, uu____5075)  in
              FStar_Syntax_Syntax.Tm_app uu____5058  in
            mk1 uu____5057
          else
            (let uu____5146 =
               let uu____5152 =
                 let uu____5154 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5154
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5152)  in
             FStar_Errors.raise_err uu____5146)
      | FStar_Syntax_Syntax.Tm_bvar uu____5158 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5159 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5160 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5161 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5189 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5189 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___511_5197 = env  in
                 let uu____5198 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5198;
                   subst = (uu___511_5197.subst);
                   tc_const = (uu___511_5197.tc_const)
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
               ((let uu___526_5225 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___526_5225.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___526_5225.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5232 =
            let uu____5233 =
              let uu____5240 = star_type' env t2  in (uu____5240, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5233  in
          mk1 uu____5232
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5292 =
            let uu____5293 =
              let uu____5320 = star_type' env e  in
              let uu____5323 =
                let uu____5340 =
                  let uu____5349 = star_type' env t2  in
                  FStar_Util.Inl uu____5349  in
                (uu____5340, FStar_Pervasives_Native.None)  in
              (uu____5320, uu____5323, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5293  in
          mk1 uu____5292
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5437 =
            let uu____5438 =
              let uu____5465 = star_type' env e  in
              let uu____5468 =
                let uu____5485 =
                  let uu____5494 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5494  in
                (uu____5485, FStar_Pervasives_Native.None)  in
              (uu____5465, uu____5468, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5438  in
          mk1 uu____5437
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5535,(uu____5536,FStar_Pervasives_Native.Some uu____5537),uu____5538)
          ->
          let uu____5587 =
            let uu____5593 =
              let uu____5595 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5595
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5593)  in
          FStar_Errors.raise_err uu____5587
      | FStar_Syntax_Syntax.Tm_refine uu____5599 ->
          let uu____5606 =
            let uu____5612 =
              let uu____5614 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5614
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5612)  in
          FStar_Errors.raise_err uu____5606
      | FStar_Syntax_Syntax.Tm_uinst uu____5618 ->
          let uu____5625 =
            let uu____5631 =
              let uu____5633 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5633
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5631)  in
          FStar_Errors.raise_err uu____5625
      | FStar_Syntax_Syntax.Tm_quoted uu____5637 ->
          let uu____5644 =
            let uu____5650 =
              let uu____5652 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5652
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5650)  in
          FStar_Errors.raise_err uu____5644
      | FStar_Syntax_Syntax.Tm_constant uu____5656 ->
          let uu____5657 =
            let uu____5663 =
              let uu____5665 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5665
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5663)  in
          FStar_Errors.raise_err uu____5657
      | FStar_Syntax_Syntax.Tm_match uu____5669 ->
          let uu____5692 =
            let uu____5698 =
              let uu____5700 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5700
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5698)  in
          FStar_Errors.raise_err uu____5692
      | FStar_Syntax_Syntax.Tm_let uu____5704 ->
          let uu____5718 =
            let uu____5724 =
              let uu____5726 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5726
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5724)  in
          FStar_Errors.raise_err uu____5718
      | FStar_Syntax_Syntax.Tm_uvar uu____5730 ->
          let uu____5743 =
            let uu____5749 =
              let uu____5751 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5751
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5749)  in
          FStar_Errors.raise_err uu____5743
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5755 =
            let uu____5761 =
              let uu____5763 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5763
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5761)  in
          FStar_Errors.raise_err uu____5755
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5768 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5768
      | FStar_Syntax_Syntax.Tm_delayed uu____5771 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_5803  ->
    match uu___3_5803 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_5814  ->
                match uu___2_5814 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5817 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5827 =
      let uu____5828 = FStar_Syntax_Subst.compress t  in
      uu____5828.FStar_Syntax_Syntax.n  in
    match uu____5827 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5860 =
            let uu____5861 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5861  in
          is_C uu____5860  in
        if r
        then
          ((let uu____5885 =
              let uu____5887 =
                FStar_List.for_all
                  (fun uu____5898  ->
                     match uu____5898 with | (h,uu____5907) -> is_C h) args
                 in
              Prims.op_Negation uu____5887  in
            if uu____5885 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5920 =
              let uu____5922 =
                FStar_List.for_all
                  (fun uu____5934  ->
                     match uu____5934 with
                     | (h,uu____5943) ->
                         let uu____5948 = is_C h  in
                         Prims.op_Negation uu____5948) args
                 in
              Prims.op_Negation uu____5922  in
            if uu____5920 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5977 = nm_of_comp comp  in
        (match uu____5977 with
         | M t1 ->
             ((let uu____5981 = is_C t1  in
               if uu____5981 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5990) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5996) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6002,uu____6003) -> is_C t1
    | uu____6044 -> false
  
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
          let uu____6080 =
            let uu____6081 =
              let uu____6098 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6101 =
                let uu____6112 =
                  let uu____6121 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6121)  in
                [uu____6112]  in
              (uu____6098, uu____6101)  in
            FStar_Syntax_Syntax.Tm_app uu____6081  in
          mk1 uu____6080  in
        let uu____6157 =
          let uu____6158 = FStar_Syntax_Syntax.mk_binder p  in [uu____6158]
           in
        FStar_Syntax_Util.abs uu____6157 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6183  ->
    match uu___4_6183 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6186 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6424 =
          match uu____6424 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6461 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6464 =
                       let uu____6466 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6466  in
                     Prims.op_Negation uu____6464)
                   in
                if uu____6461
                then
                  let uu____6468 =
                    let uu____6474 =
                      let uu____6476 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6478 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6480 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6476 uu____6478 uu____6480
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6474)  in
                  FStar_Errors.raise_err uu____6468
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6505 = mk_return env t1 s_e  in
                     ((M t1), uu____6505, u_e)))
               | (M t1,N t2) ->
                   let uu____6512 =
                     let uu____6518 =
                       let uu____6520 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6522 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6524 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6520 uu____6522 uu____6524
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6518)
                      in
                   FStar_Errors.raise_err uu____6512)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_6576 =
            match uu___5_6576 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6592 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6613 =
                let uu____6619 =
                  let uu____6621 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6621
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6619)  in
              FStar_Errors.raise_error uu____6613 e2.FStar_Syntax_Syntax.pos
          | M uu____6631 ->
              let uu____6632 = check env1 e2 context_nm  in
              strip_m uu____6632
           in
        let uu____6639 =
          let uu____6640 = FStar_Syntax_Subst.compress e  in
          uu____6640.FStar_Syntax_Syntax.n  in
        match uu____6639 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6649 ->
            let uu____6650 = infer env e  in return_if uu____6650
        | FStar_Syntax_Syntax.Tm_name uu____6657 ->
            let uu____6658 = infer env e  in return_if uu____6658
        | FStar_Syntax_Syntax.Tm_fvar uu____6665 ->
            let uu____6666 = infer env e  in return_if uu____6666
        | FStar_Syntax_Syntax.Tm_abs uu____6673 ->
            let uu____6692 = infer env e  in return_if uu____6692
        | FStar_Syntax_Syntax.Tm_constant uu____6699 ->
            let uu____6700 = infer env e  in return_if uu____6700
        | FStar_Syntax_Syntax.Tm_quoted uu____6707 ->
            let uu____6714 = infer env e  in return_if uu____6714
        | FStar_Syntax_Syntax.Tm_app uu____6721 ->
            let uu____6738 = infer env e  in return_if uu____6738
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6746 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6746 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6811) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6817) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6823,uu____6824) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6865 ->
            let uu____6879 =
              let uu____6881 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6881  in
            failwith uu____6879
        | FStar_Syntax_Syntax.Tm_type uu____6890 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6898 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6920 ->
            let uu____6927 =
              let uu____6929 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6929  in
            failwith uu____6927
        | FStar_Syntax_Syntax.Tm_uvar uu____6938 ->
            let uu____6951 =
              let uu____6953 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6953  in
            failwith uu____6951
        | FStar_Syntax_Syntax.Tm_delayed uu____6962 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6992 =
              let uu____6994 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6994  in
            failwith uu____6992

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
      let uu____7024 =
        let uu____7025 = FStar_Syntax_Subst.compress e  in
        uu____7025.FStar_Syntax_Syntax.n  in
      match uu____7024 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7044 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7044
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7095;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7096;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7102 =
                  let uu___761_7103 = rc  in
                  let uu____7104 =
                    let uu____7109 =
                      let uu____7112 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7112  in
                    FStar_Pervasives_Native.Some uu____7109  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___761_7103.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7104;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___761_7103.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7102
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___767_7124 = env  in
            let uu____7125 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7125;
              subst = (uu___767_7124.subst);
              tc_const = (uu___767_7124.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7151  ->
                 match uu____7151 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___774_7174 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___774_7174.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___774_7174.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7175 =
            FStar_List.fold_left
              (fun uu____7206  ->
                 fun uu____7207  ->
                   match (uu____7206, uu____7207) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7265 = is_C c  in
                       if uu____7265
                       then
                         let xw =
                           let uu____7275 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7275
                            in
                         let x =
                           let uu___786_7278 = bv  in
                           let uu____7279 =
                             let uu____7282 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7282  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___786_7278.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___786_7278.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7279
                           }  in
                         let env3 =
                           let uu___789_7284 = env2  in
                           let uu____7285 =
                             let uu____7288 =
                               let uu____7289 =
                                 let uu____7296 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7296)  in
                               FStar_Syntax_Syntax.NT uu____7289  in
                             uu____7288 :: (env2.subst)  in
                           {
                             tcenv = (uu___789_7284.tcenv);
                             subst = uu____7285;
                             tc_const = (uu___789_7284.tc_const)
                           }  in
                         let uu____7301 =
                           let uu____7304 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7305 =
                             let uu____7308 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7308 :: acc  in
                           uu____7304 :: uu____7305  in
                         (env3, uu____7301)
                       else
                         (let x =
                            let uu___792_7314 = bv  in
                            let uu____7315 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___792_7314.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___792_7314.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7315
                            }  in
                          let uu____7318 =
                            let uu____7321 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7321 :: acc  in
                          (env2, uu____7318))) (env1, []) binders1
             in
          (match uu____7175 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7341 =
                 let check_what =
                   let uu____7367 = is_monadic rc_opt1  in
                   if uu____7367 then check_m else check_n  in
                 let uu____7384 = check_what env2 body1  in
                 match uu____7384 with
                 | (t,s_body,u_body) ->
                     let uu____7404 =
                       let uu____7407 =
                         let uu____7408 = is_monadic rc_opt1  in
                         if uu____7408 then M t else N t  in
                       comp_of_nm uu____7407  in
                     (uu____7404, s_body, u_body)
                  in
               (match uu____7341 with
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
                                 let uu____7448 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7454  ->
                                           match uu___6_7454 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7457 -> false))
                                    in
                                 if uu____7448
                                 then
                                   let uu____7460 =
                                     FStar_List.filter
                                       (fun uu___7_7464  ->
                                          match uu___7_7464 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7467 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7460
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7478 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7484  ->
                                         match uu___8_7484 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7487 -> false))
                                  in
                               if uu____7478
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7496  ->
                                        match uu___9_7496 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7499 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7501 =
                                   let uu____7502 =
                                     let uu____7507 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7507
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7502 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7501
                               else
                                 (let uu____7514 =
                                    let uu___833_7515 = rc  in
                                    let uu____7516 =
                                      let uu____7521 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7521
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___833_7515.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7516;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___833_7515.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7514))
                       in
                    let uu____7526 =
                      let comp1 =
                        let uu____7534 = is_monadic rc_opt1  in
                        let uu____7536 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7534 uu____7536
                         in
                      let uu____7537 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7537,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7526 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7575 =
                             let uu____7576 =
                               let uu____7595 =
                                 let uu____7598 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7598 s_rc_opt  in
                               (s_binders1, s_body1, uu____7595)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7576  in
                           mk1 uu____7575  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7618 =
                             let uu____7619 =
                               let uu____7638 =
                                 let uu____7641 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7641 u_rc_opt  in
                               (u_binders2, u_body2, uu____7638)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7619  in
                           mk1 uu____7618  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7657;_};
            FStar_Syntax_Syntax.fv_delta = uu____7658;
            FStar_Syntax_Syntax.fv_qual = uu____7659;_}
          ->
          let uu____7662 =
            let uu____7667 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7667  in
          (match uu____7662 with
           | (uu____7698,t) ->
               let uu____7700 =
                 let uu____7701 = normalize1 t  in N uu____7701  in
               (uu____7700, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7702;
             FStar_Syntax_Syntax.vars = uu____7703;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7782 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7782 with
           | (unary_op1,uu____7806) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7877;
             FStar_Syntax_Syntax.vars = uu____7878;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7974 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7974 with
           | (unary_op1,uu____7998) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8077;
             FStar_Syntax_Syntax.vars = uu____8078;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8116 = infer env a  in
          (match uu____8116 with
           | (t,s,u) ->
               let uu____8132 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8132 with
                | (head1,uu____8156) ->
                    let uu____8181 =
                      let uu____8182 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8182  in
                    let uu____8183 =
                      let uu____8184 =
                        let uu____8185 =
                          let uu____8202 =
                            let uu____8213 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8213]  in
                          (head1, uu____8202)  in
                        FStar_Syntax_Syntax.Tm_app uu____8185  in
                      mk1 uu____8184  in
                    let uu____8250 =
                      let uu____8251 =
                        let uu____8252 =
                          let uu____8269 =
                            let uu____8280 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8280]  in
                          (head1, uu____8269)  in
                        FStar_Syntax_Syntax.Tm_app uu____8252  in
                      mk1 uu____8251  in
                    (uu____8181, uu____8183, uu____8250)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8317;
             FStar_Syntax_Syntax.vars = uu____8318;_},(a1,uu____8320)::a2::[])
          ->
          let uu____8376 = infer env a1  in
          (match uu____8376 with
           | (t,s,u) ->
               let uu____8392 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8392 with
                | (head1,uu____8416) ->
                    let uu____8441 =
                      let uu____8442 =
                        let uu____8443 =
                          let uu____8460 =
                            let uu____8471 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8471; a2]  in
                          (head1, uu____8460)  in
                        FStar_Syntax_Syntax.Tm_app uu____8443  in
                      mk1 uu____8442  in
                    let uu____8516 =
                      let uu____8517 =
                        let uu____8518 =
                          let uu____8535 =
                            let uu____8546 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8546; a2]  in
                          (head1, uu____8535)  in
                        FStar_Syntax_Syntax.Tm_app uu____8518  in
                      mk1 uu____8517  in
                    (t, uu____8441, uu____8516)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8591;
             FStar_Syntax_Syntax.vars = uu____8592;_},uu____8593)
          ->
          let uu____8618 =
            let uu____8624 =
              let uu____8626 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8626
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8624)  in
          FStar_Errors.raise_error uu____8618 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8636;
             FStar_Syntax_Syntax.vars = uu____8637;_},uu____8638)
          ->
          let uu____8663 =
            let uu____8669 =
              let uu____8671 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8671
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8669)  in
          FStar_Errors.raise_error uu____8663 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8707 = check_n env head1  in
          (match uu____8707 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8730 =
                   let uu____8731 = FStar_Syntax_Subst.compress t  in
                   uu____8731.FStar_Syntax_Syntax.n  in
                 match uu____8730 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8735 -> true
                 | uu____8751 -> false  in
               let rec flatten1 t =
                 let uu____8773 =
                   let uu____8774 = FStar_Syntax_Subst.compress t  in
                   uu____8774.FStar_Syntax_Syntax.n  in
                 match uu____8773 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8793);
                                FStar_Syntax_Syntax.pos = uu____8794;
                                FStar_Syntax_Syntax.vars = uu____8795;_})
                     when is_arrow t1 ->
                     let uu____8824 = flatten1 t1  in
                     (match uu____8824 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8924,uu____8925)
                     -> flatten1 e1
                 | uu____8966 ->
                     let uu____8967 =
                       let uu____8973 =
                         let uu____8975 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____8975
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____8973)  in
                     FStar_Errors.raise_err uu____8967
                  in
               let uu____8993 = flatten1 t_head  in
               (match uu____8993 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9068 =
                          let uu____9074 =
                            let uu____9076 = FStar_Util.string_of_int n1  in
                            let uu____9078 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9080 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9076 uu____9078 uu____9080
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9074)
                           in
                        FStar_Errors.raise_err uu____9068)
                     else ();
                     (let uu____9086 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9086 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9139 args1 =
                            match uu____9139 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9239 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9239
                                 | (binders3,[]) ->
                                     let uu____9277 =
                                       let uu____9278 =
                                         let uu____9281 =
                                           let uu____9282 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9282
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9281
                                          in
                                       uu____9278.FStar_Syntax_Syntax.n  in
                                     (match uu____9277 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9315 =
                                            let uu____9316 =
                                              let uu____9317 =
                                                let uu____9332 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9332)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9317
                                               in
                                            mk1 uu____9316  in
                                          N uu____9315
                                      | uu____9345 -> failwith "wat?")
                                 | ([],uu____9347::uu____9348) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9401)::binders3,(arg,uu____9404)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9491 = FStar_List.splitAt n' binders1  in
                          (match uu____9491 with
                           | (binders2,uu____9525) ->
                               let uu____9558 =
                                 let uu____9581 =
                                   FStar_List.map2
                                     (fun uu____9643  ->
                                        fun uu____9644  ->
                                          match (uu____9643, uu____9644) with
                                          | ((bv,uu____9692),(arg,q)) ->
                                              let uu____9721 =
                                                let uu____9722 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9722.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9721 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9743 ->
                                                   let uu____9744 =
                                                     let uu____9751 =
                                                       star_type' env arg  in
                                                     (uu____9751, q)  in
                                                   (uu____9744, [(arg, q)])
                                               | uu____9788 ->
                                                   let uu____9789 =
                                                     check_n env arg  in
                                                   (match uu____9789 with
                                                    | (uu____9814,s_arg,u_arg)
                                                        ->
                                                        let uu____9817 =
                                                          let uu____9826 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9826
                                                          then
                                                            let uu____9837 =
                                                              let uu____9844
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9844, q)
                                                               in
                                                            [uu____9837;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9817))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9581  in
                               (match uu____9558 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____9972 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____9985 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____9972, uu____9985)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10054) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10060) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10066,uu____10067) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10109 =
            let uu____10110 = env.tc_const c  in N uu____10110  in
          (uu____10109, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10117 ->
          let uu____10131 =
            let uu____10133 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10133  in
          failwith uu____10131
      | FStar_Syntax_Syntax.Tm_type uu____10142 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10150 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10172 ->
          let uu____10179 =
            let uu____10181 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10181  in
          failwith uu____10179
      | FStar_Syntax_Syntax.Tm_uvar uu____10190 ->
          let uu____10203 =
            let uu____10205 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10205  in
          failwith uu____10203
      | FStar_Syntax_Syntax.Tm_delayed uu____10214 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10244 =
            let uu____10246 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10246  in
          failwith uu____10244

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
          let uu____10295 = check_n env e0  in
          match uu____10295 with
          | (uu____10308,s_e0,u_e0) ->
              let uu____10311 =
                let uu____10340 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10401 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10401 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1108_10443 = env  in
                             let uu____10444 =
                               let uu____10445 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10445
                                in
                             {
                               tcenv = uu____10444;
                               subst = (uu___1108_10443.subst);
                               tc_const = (uu___1108_10443.tc_const)
                             }  in
                           let uu____10448 = f env1 body  in
                           (match uu____10448 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10520 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10340  in
              (match uu____10311 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10626 = FStar_List.hd nms  in
                     match uu____10626 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10635  ->
                          match uu___10_10635 with
                          | M uu____10637 -> true
                          | uu____10639 -> false) nms
                      in
                   let uu____10641 =
                     let uu____10678 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10768  ->
                              match uu____10768 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____10952 =
                                         check env original_body (M t2)  in
                                       (match uu____10952 with
                                        | (uu____10989,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11028,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10678  in
                   (match uu____10641 with
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
                              (fun uu____11217  ->
                                 match uu____11217 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11268 =
                                         let uu____11269 =
                                           let uu____11286 =
                                             let uu____11297 =
                                               let uu____11306 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11309 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11306, uu____11309)  in
                                             [uu____11297]  in
                                           (s_body, uu____11286)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11269
                                          in
                                       mk1 uu____11268  in
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
                            let uu____11444 =
                              let uu____11445 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11445]  in
                            let uu____11464 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11444 uu____11464
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11488 =
                              let uu____11497 =
                                let uu____11504 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11504
                                 in
                              [uu____11497]  in
                            let uu____11523 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11488 uu____11523
                             in
                          let uu____11526 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11565 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11526, uu____11565)
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
                           let uu____11675 =
                             let uu____11676 =
                               let uu____11677 =
                                 let uu____11704 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11704,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11677
                                in
                             mk1 uu____11676  in
                           let uu____11763 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11675, uu____11763))))

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
              let uu____11828 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11828]  in
            let uu____11847 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11847 with
            | (x_binders1,e21) ->
                let uu____11860 = infer env e1  in
                (match uu____11860 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____11877 = is_C t1  in
                       if uu____11877
                       then
                         let uu___1194_11880 = binding  in
                         let uu____11881 =
                           let uu____11884 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____11884  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1194_11880.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1194_11880.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11881;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1194_11880.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1194_11880.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1194_11880.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1194_11880.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1197_11888 = env  in
                       let uu____11889 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1199_11891 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1199_11891.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1199_11891.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11889;
                         subst = (uu___1197_11888.subst);
                         tc_const = (uu___1197_11888.tc_const)
                       }  in
                     let uu____11892 = proceed env1 e21  in
                     (match uu____11892 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1206_11909 = binding  in
                            let uu____11910 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1206_11909.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1206_11909.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11910;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1206_11909.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1206_11909.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1206_11909.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1206_11909.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____11913 =
                            let uu____11914 =
                              let uu____11915 =
                                let uu____11929 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1209_11946 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1209_11946.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1209_11946.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1209_11946.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1209_11946.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1209_11946.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1209_11946.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11929)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11915  in
                            mk1 uu____11914  in
                          let uu____11947 =
                            let uu____11948 =
                              let uu____11949 =
                                let uu____11963 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1211_11980 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1211_11980.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1211_11980.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1211_11980.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1211_11980.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1211_11980.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1211_11980.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11963)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11949  in
                            mk1 uu____11948  in
                          (nm_rec, uu____11913, uu____11947))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1218_11985 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1218_11985.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1218_11985.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1218_11985.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1218_11985.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1218_11985.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1221_11987 = env  in
                       let uu____11988 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1223_11990 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1223_11990.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1223_11990.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11988;
                         subst = (uu___1221_11987.subst);
                         tc_const = (uu___1221_11987.tc_const)
                       }  in
                     let uu____11991 = ensure_m env1 e21  in
                     (match uu____11991 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12015 =
                              let uu____12016 =
                                let uu____12033 =
                                  let uu____12044 =
                                    let uu____12053 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12056 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12053, uu____12056)  in
                                  [uu____12044]  in
                                (s_e2, uu____12033)  in
                              FStar_Syntax_Syntax.Tm_app uu____12016  in
                            mk1 uu____12015  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12098 =
                              let uu____12099 =
                                let uu____12116 =
                                  let uu____12127 =
                                    let uu____12136 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12136)  in
                                  [uu____12127]  in
                                (s_e1, uu____12116)  in
                              FStar_Syntax_Syntax.Tm_app uu____12099  in
                            mk1 uu____12098  in
                          let uu____12172 =
                            let uu____12173 =
                              let uu____12174 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12174]  in
                            FStar_Syntax_Util.abs uu____12173 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12193 =
                            let uu____12194 =
                              let uu____12195 =
                                let uu____12209 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1235_12226 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1235_12226.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1235_12226.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1235_12226.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1235_12226.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1235_12226.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1235_12226.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12209)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12195  in
                            mk1 uu____12194  in
                          ((M t2), uu____12172, uu____12193)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12236 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12236  in
      let uu____12237 = check env e mn  in
      match uu____12237 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12253 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12276 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12276  in
      let uu____12277 = check env e mn  in
      match uu____12277 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12293 -> failwith "[check_m]: impossible"

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
        (let uu____12326 =
           let uu____12328 = is_C c  in Prims.op_Negation uu____12328  in
         if uu____12326 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12342 =
           let uu____12343 = FStar_Syntax_Subst.compress c  in
           uu____12343.FStar_Syntax_Syntax.n  in
         match uu____12342 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12372 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12372 with
              | (wp_head,wp_args) ->
                  ((let uu____12416 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12435 =
                           let uu____12437 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12437
                            in
                         Prims.op_Negation uu____12435)
                       in
                    if uu____12416 then failwith "mismatch" else ());
                   (let uu____12450 =
                      let uu____12451 =
                        let uu____12468 =
                          FStar_List.map2
                            (fun uu____12506  ->
                               fun uu____12507  ->
                                 match (uu____12506, uu____12507) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12569 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12569
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12578 =
                                         let uu____12580 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12580 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12578
                                       then
                                         let uu____12582 =
                                           let uu____12588 =
                                             let uu____12590 =
                                               print_implicit q  in
                                             let uu____12592 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12590 uu____12592
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12588)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12582
                                       else ());
                                      (let uu____12598 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12598, q)))) args wp_args
                           in
                        (head1, uu____12468)  in
                      FStar_Syntax_Syntax.Tm_app uu____12451  in
                    mk1 uu____12450)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12644 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12644 with
              | (binders_orig,comp1) ->
                  let uu____12651 =
                    let uu____12668 =
                      FStar_List.map
                        (fun uu____12708  ->
                           match uu____12708 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12736 = is_C h  in
                               if uu____12736
                               then
                                 let w' =
                                   let uu____12752 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12752
                                    in
                                 let uu____12754 =
                                   let uu____12763 =
                                     let uu____12772 =
                                       let uu____12779 =
                                         let uu____12780 =
                                           let uu____12781 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12781  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12780
                                          in
                                       (uu____12779, q)  in
                                     [uu____12772]  in
                                   (w', q) :: uu____12763  in
                                 (w', uu____12754)
                               else
                                 (let x =
                                    let uu____12815 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____12815
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12668  in
                  (match uu____12651 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____12889 =
                           let uu____12892 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12892
                            in
                         FStar_Syntax_Subst.subst_comp uu____12889 comp1  in
                       let app =
                         let uu____12896 =
                           let uu____12897 =
                             let uu____12914 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____12933 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____12934 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12933, uu____12934)) bvs
                                in
                             (wp, uu____12914)  in
                           FStar_Syntax_Syntax.Tm_app uu____12897  in
                         mk1 uu____12896  in
                       let comp3 =
                         let uu____12949 = type_of_comp comp2  in
                         let uu____12950 = is_monadic_comp comp2  in
                         trans_G env uu____12949 uu____12950 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____12953,uu____12954) ->
             trans_F_ env e wp
         | uu____12995 -> failwith "impossible trans_F_")

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
            let uu____13003 =
              let uu____13004 = star_type' env h  in
              let uu____13007 =
                let uu____13018 =
                  let uu____13027 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13027)  in
                [uu____13018]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13004;
                FStar_Syntax_Syntax.effect_args = uu____13007;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13003
          else
            (let uu____13053 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13053)

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
    fun t  -> let uu____13074 = n env.tcenv t  in star_type' env uu____13074
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13094 = n env.tcenv t  in check_n env uu____13094
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13111 = n env.tcenv c  in
        let uu____13112 = n env.tcenv wp  in
        trans_F_ env uu____13111 uu____13112
  