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
               let t1 = FStar_Syntax_Util.unascribe t  in
               let uu____169 =
                 let uu____170 = FStar_Syntax_Subst.compress t1  in
                 uu____170.FStar_Syntax_Syntax.n  in
               match uu____169 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t2,uu____205) -> t2
                     | uu____214 ->
                         let uu____215 =
                           let uu____221 =
                             let uu____223 =
                               FStar_Syntax_Print.comp_to_string comp  in
                             FStar_Util.format1
                               "wp_a contains non-Tot arrow: %s" uu____223
                              in
                           (FStar_Errors.Error_UnexpectedDM4FType, uu____221)
                            in
                         FStar_Errors.raise_error uu____215
                           comp.FStar_Syntax_Syntax.pos
                      in
                   let uu____227 = collect_binders rest  in
                   FStar_List.append bs uu____227
               | FStar_Syntax_Syntax.Tm_type uu____242 -> []
               | uu____249 ->
                   let uu____250 =
                     let uu____256 =
                       let uu____258 = FStar_Syntax_Print.term_to_string t1
                          in
                       FStar_Util.format1
                         "wp_a doesn't end in Type0, but rather in %s"
                         uu____258
                        in
                     (FStar_Errors.Error_UnexpectedDM4FType, uu____256)  in
                   FStar_Errors.raise_error uu____250
                     t1.FStar_Syntax_Syntax.pos
                in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____287 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____287 FStar_Syntax_Util.name_binders
                in
             (let uu____313 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____313
              then
                let uu____317 =
                  let uu____319 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____319  in
                d uu____317
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____357 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____357 with
                | (sigelt,fv) ->
                    ((let uu____365 =
                        let uu____368 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____368
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____365);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____448  ->
                     match uu____448 with
                     | (t,b) ->
                         let uu____462 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____462))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____501 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____501))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____535 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____535)
                 in
              let uu____538 =
                let uu____555 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____580 =
                        let uu____583 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____583  in
                      FStar_Syntax_Util.arrow gamma uu____580  in
                    let uu____584 =
                      let uu____585 =
                        let uu____594 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____601 =
                          let uu____610 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____610]  in
                        uu____594 :: uu____601  in
                      FStar_List.append binders uu____585  in
                    FStar_Syntax_Util.abs uu____584 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____641 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____642 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____641, uu____642)  in
                match uu____555 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____684 =
                        let uu____685 =
                          let uu____702 =
                            let uu____713 =
                              FStar_List.map
                                (fun uu____735  ->
                                   match uu____735 with
                                   | (bv,uu____747) ->
                                       let uu____752 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____753 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____752, uu____753)) binders
                               in
                            let uu____755 =
                              let uu____762 =
                                let uu____767 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____768 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____767, uu____768)  in
                              let uu____770 =
                                let uu____777 =
                                  let uu____782 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____782)  in
                                [uu____777]  in
                              uu____762 :: uu____770  in
                            FStar_List.append uu____713 uu____755  in
                          (fv, uu____702)  in
                        FStar_Syntax_Syntax.Tm_app uu____685  in
                      mk1 uu____684  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____538 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____855 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____855
                       in
                    let ret1 =
                      let uu____860 =
                        let uu____861 =
                          let uu____864 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____864  in
                        FStar_Syntax_Util.residual_tot uu____861  in
                      FStar_Pervasives_Native.Some uu____860  in
                    let body =
                      let uu____868 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____868 ret1  in
                    let uu____871 =
                      let uu____872 = mk_all_implicit binders  in
                      let uu____879 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____872 uu____879  in
                    FStar_Syntax_Util.abs uu____871 body ret1  in
                  let c_pure1 =
                    let uu____917 = mk_lid "pure"  in
                    register env1 uu____917 c_pure  in
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
                      let uu____927 =
                        let uu____928 =
                          let uu____929 =
                            let uu____938 =
                              let uu____945 =
                                let uu____946 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____946
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____945  in
                            [uu____938]  in
                          let uu____959 =
                            let uu____962 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____962  in
                          FStar_Syntax_Util.arrow uu____929 uu____959  in
                        mk_gctx uu____928  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____927
                       in
                    let r =
                      let uu____965 =
                        let uu____966 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____966  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____965
                       in
                    let ret1 =
                      let uu____971 =
                        let uu____972 =
                          let uu____975 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____975  in
                        FStar_Syntax_Util.residual_tot uu____972  in
                      FStar_Pervasives_Native.Some uu____971  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____985 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____988 =
                          let uu____999 =
                            let uu____1002 =
                              let uu____1003 =
                                let uu____1004 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____1004
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1003  in
                            [uu____1002]  in
                          FStar_List.append gamma_as_args uu____999  in
                        FStar_Syntax_Util.mk_app uu____985 uu____988  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____1007 =
                      let uu____1008 = mk_all_implicit binders  in
                      let uu____1015 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____1008 uu____1015  in
                    FStar_Syntax_Util.abs uu____1007 outer_body ret1  in
                  let c_app1 =
                    let uu____1067 = mk_lid "app"  in
                    register env1 uu____1067 c_app  in
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
                      let uu____1079 =
                        let uu____1088 =
                          let uu____1095 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1095  in
                        [uu____1088]  in
                      let uu____1108 =
                        let uu____1111 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1111  in
                      FStar_Syntax_Util.arrow uu____1079 uu____1108  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1115 =
                        let uu____1116 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1116  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1115
                       in
                    let ret1 =
                      let uu____1121 =
                        let uu____1122 =
                          let uu____1125 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1125  in
                        FStar_Syntax_Util.residual_tot uu____1122  in
                      FStar_Pervasives_Native.Some uu____1121  in
                    let uu____1126 =
                      let uu____1127 = mk_all_implicit binders  in
                      let uu____1134 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1127 uu____1134  in
                    let uu____1185 =
                      let uu____1188 =
                        let uu____1199 =
                          let uu____1202 =
                            let uu____1203 =
                              let uu____1214 =
                                let uu____1217 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1217]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1214
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1203  in
                          let uu____1226 =
                            let uu____1229 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1229]  in
                          uu____1202 :: uu____1226  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1199
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1188  in
                    FStar_Syntax_Util.abs uu____1126 uu____1185 ret1  in
                  let c_lift11 =
                    let uu____1239 = mk_lid "lift1"  in
                    register env1 uu____1239 c_lift1  in
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
                      let uu____1253 =
                        let uu____1262 =
                          let uu____1269 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1269  in
                        let uu____1270 =
                          let uu____1279 =
                            let uu____1286 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1286  in
                          [uu____1279]  in
                        uu____1262 :: uu____1270  in
                      let uu____1305 =
                        let uu____1308 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1308  in
                      FStar_Syntax_Util.arrow uu____1253 uu____1305  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1312 =
                        let uu____1313 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1313  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1312
                       in
                    let a2 =
                      let uu____1316 =
                        let uu____1317 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1317  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1316
                       in
                    let ret1 =
                      let uu____1322 =
                        let uu____1323 =
                          let uu____1326 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1326  in
                        FStar_Syntax_Util.residual_tot uu____1323  in
                      FStar_Pervasives_Native.Some uu____1322  in
                    let uu____1327 =
                      let uu____1328 = mk_all_implicit binders  in
                      let uu____1335 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1328 uu____1335  in
                    let uu____1400 =
                      let uu____1403 =
                        let uu____1414 =
                          let uu____1417 =
                            let uu____1418 =
                              let uu____1429 =
                                let uu____1432 =
                                  let uu____1433 =
                                    let uu____1444 =
                                      let uu____1447 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1447]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1444
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1433
                                   in
                                let uu____1456 =
                                  let uu____1459 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1459]  in
                                uu____1432 :: uu____1456  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1429
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1418  in
                          let uu____1468 =
                            let uu____1471 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1471]  in
                          uu____1417 :: uu____1468  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1414
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1403  in
                    FStar_Syntax_Util.abs uu____1327 uu____1400 ret1  in
                  let c_lift21 =
                    let uu____1481 = mk_lid "lift2"  in
                    register env1 uu____1481 c_lift2  in
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
                      let uu____1493 =
                        let uu____1502 =
                          let uu____1509 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1509  in
                        [uu____1502]  in
                      let uu____1522 =
                        let uu____1525 =
                          let uu____1526 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1526  in
                        FStar_Syntax_Syntax.mk_Total uu____1525  in
                      FStar_Syntax_Util.arrow uu____1493 uu____1522  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1532 =
                        let uu____1533 =
                          let uu____1536 =
                            let uu____1537 =
                              let uu____1546 =
                                let uu____1553 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1553
                                 in
                              [uu____1546]  in
                            let uu____1566 =
                              let uu____1569 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1569  in
                            FStar_Syntax_Util.arrow uu____1537 uu____1566  in
                          mk_ctx uu____1536  in
                        FStar_Syntax_Util.residual_tot uu____1533  in
                      FStar_Pervasives_Native.Some uu____1532  in
                    let e1 =
                      let uu____1571 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1571
                       in
                    let body =
                      let uu____1576 =
                        let uu____1577 =
                          let uu____1586 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1586]  in
                        FStar_List.append gamma uu____1577  in
                      let uu____1611 =
                        let uu____1614 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1617 =
                          let uu____1628 =
                            let uu____1629 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1629  in
                          let uu____1630 = args_of_binders1 gamma  in
                          uu____1628 :: uu____1630  in
                        FStar_Syntax_Util.mk_app uu____1614 uu____1617  in
                      FStar_Syntax_Util.abs uu____1576 uu____1611 ret1  in
                    let uu____1633 =
                      let uu____1634 = mk_all_implicit binders  in
                      let uu____1641 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1634 uu____1641  in
                    FStar_Syntax_Util.abs uu____1633 body ret1  in
                  let c_push1 =
                    let uu____1686 = mk_lid "push"  in
                    register env1 uu____1686 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > Prims.int_zero
                    then
                      let uu____1713 =
                        let uu____1714 =
                          let uu____1731 = args_of_binders1 binders  in
                          (c, uu____1731)  in
                        FStar_Syntax_Syntax.Tm_app uu____1714  in
                      mk1 uu____1713
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1760 =
                        let uu____1761 =
                          let uu____1770 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1777 =
                            let uu____1786 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1786]  in
                          uu____1770 :: uu____1777  in
                        let uu____1811 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1761 uu____1811  in
                      FStar_Syntax_Syntax.mk_Total uu____1760  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1816 =
                      let uu____1817 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1817  in
                    let uu____1832 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.of_int (2))) FStar_Pervasives_Native.None
                         in
                      let uu____1837 =
                        let uu____1840 =
                          let uu____1851 =
                            let uu____1854 =
                              let uu____1855 =
                                let uu____1866 =
                                  let uu____1875 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1875  in
                                [uu____1866]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1855  in
                            [uu____1854]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1851
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1840  in
                      FStar_Syntax_Util.ascribe uu____1837
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1816 uu____1832
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1919 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1919 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1932 =
                        let uu____1941 =
                          let uu____1948 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1948  in
                        [uu____1941]  in
                      let uu____1961 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1932 uu____1961  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1969 =
                        let uu____1980 =
                          let uu____1983 =
                            let uu____1984 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1984  in
                          let uu____2003 =
                            let uu____2006 =
                              let uu____2007 =
                                let uu____2018 =
                                  let uu____2021 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2021]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2018
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2007  in
                            [uu____2006]  in
                          uu____1983 :: uu____2003  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1980
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1969  in
                    let uu____2038 =
                      let uu____2039 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2039  in
                    FStar_Syntax_Util.abs uu____2038 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2055 = mk_lid "wp_close"  in
                    register env1 uu____2055 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2066 =
                      let uu____2067 =
                        let uu____2068 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left
                          FStar_TypeChecker_Common.lcomp_of_comp uu____2068
                         in
                      FStar_TypeChecker_Common.residual_comp_of_lcomp
                        uu____2067
                       in
                    FStar_Pervasives_Native.Some uu____2066  in
                  let mk_forall1 x body =
                    let uu____2080 =
                      let uu____2087 =
                        let uu____2088 =
                          let uu____2105 =
                            let uu____2116 =
                              let uu____2125 =
                                let uu____2126 =
                                  let uu____2127 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2127]  in
                                FStar_Syntax_Util.abs uu____2126 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2125  in
                            [uu____2116]  in
                          (FStar_Syntax_Util.tforall, uu____2105)  in
                        FStar_Syntax_Syntax.Tm_app uu____2088  in
                      FStar_Syntax_Syntax.mk uu____2087  in
                    uu____2080 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2185 =
                      let uu____2186 = FStar_Syntax_Subst.compress t  in
                      uu____2186.FStar_Syntax_Syntax.n  in
                    match uu____2185 with
                    | FStar_Syntax_Syntax.Tm_type uu____2190 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2223  ->
                              match uu____2223 with
                              | (b,uu____2232) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2237 -> true  in
                  let rec is_monotonic t =
                    let uu____2250 =
                      let uu____2251 = FStar_Syntax_Subst.compress t  in
                      uu____2251.FStar_Syntax_Syntax.n  in
                    match uu____2250 with
                    | FStar_Syntax_Syntax.Tm_type uu____2255 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2288  ->
                              match uu____2288 with
                              | (b,uu____2297) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2302 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2376 =
                      let uu____2377 = FStar_Syntax_Subst.compress t1  in
                      uu____2377.FStar_Syntax_Syntax.n  in
                    match uu____2376 with
                    | FStar_Syntax_Syntax.Tm_type uu____2382 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2385);
                                      FStar_Syntax_Syntax.pos = uu____2386;
                                      FStar_Syntax_Syntax.vars = uu____2387;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2431 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2431
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2441 =
                              let uu____2444 =
                                let uu____2455 =
                                  let uu____2464 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2464  in
                                [uu____2455]  in
                              FStar_Syntax_Util.mk_app x uu____2444  in
                            let uu____2481 =
                              let uu____2484 =
                                let uu____2495 =
                                  let uu____2504 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2504  in
                                [uu____2495]  in
                              FStar_Syntax_Util.mk_app y uu____2484  in
                            mk_rel1 b uu____2441 uu____2481  in
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
                             let uu____2528 =
                               let uu____2531 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2534 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2531 uu____2534  in
                             let uu____2537 =
                               let uu____2540 =
                                 let uu____2543 =
                                   let uu____2554 =
                                     let uu____2563 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2563
                                      in
                                   [uu____2554]  in
                                 FStar_Syntax_Util.mk_app x uu____2543  in
                               let uu____2580 =
                                 let uu____2583 =
                                   let uu____2594 =
                                     let uu____2603 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2603
                                      in
                                   [uu____2594]  in
                                 FStar_Syntax_Util.mk_app y uu____2583  in
                               mk_rel1 b uu____2540 uu____2580  in
                             FStar_Syntax_Util.mk_imp uu____2528 uu____2537
                              in
                           let uu____2620 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2620)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2623);
                                      FStar_Syntax_Syntax.pos = uu____2624;
                                      FStar_Syntax_Syntax.vars = uu____2625;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2669 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2669
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2679 =
                              let uu____2682 =
                                let uu____2693 =
                                  let uu____2702 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2702  in
                                [uu____2693]  in
                              FStar_Syntax_Util.mk_app x uu____2682  in
                            let uu____2719 =
                              let uu____2722 =
                                let uu____2733 =
                                  let uu____2742 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2742  in
                                [uu____2733]  in
                              FStar_Syntax_Util.mk_app y uu____2722  in
                            mk_rel1 b uu____2679 uu____2719  in
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
                             let uu____2766 =
                               let uu____2769 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2772 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2769 uu____2772  in
                             let uu____2775 =
                               let uu____2778 =
                                 let uu____2781 =
                                   let uu____2792 =
                                     let uu____2801 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2801
                                      in
                                   [uu____2792]  in
                                 FStar_Syntax_Util.mk_app x uu____2781  in
                               let uu____2818 =
                                 let uu____2821 =
                                   let uu____2832 =
                                     let uu____2841 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2841
                                      in
                                   [uu____2832]  in
                                 FStar_Syntax_Util.mk_app y uu____2821  in
                               mk_rel1 b uu____2778 uu____2818  in
                             FStar_Syntax_Util.mk_imp uu____2766 uu____2775
                              in
                           let uu____2858 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2858)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___229_2897 = t1  in
                          let uu____2898 =
                            let uu____2899 =
                              let uu____2914 =
                                let uu____2917 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2917  in
                              ([binder], uu____2914)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2899  in
                          {
                            FStar_Syntax_Syntax.n = uu____2898;
                            FStar_Syntax_Syntax.pos =
                              (uu___229_2897.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___229_2897.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow ([],uu____2940) ->
                        failwith "impossible: arrow with empty binders"
                    | uu____2962 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____2999 =
                        let uu____3000 = FStar_Syntax_Subst.compress t1  in
                        uu____3000.FStar_Syntax_Syntax.n  in
                      match uu____2999 with
                      | FStar_Syntax_Syntax.Tm_type uu____3003 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3030 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3030
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3051 =
                                let uu____3052 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3052 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3051
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   Prims.int_one)
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3082 =
                            let uu____3093 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3111  ->
                                     match uu____3111 with
                                     | (t2,q) ->
                                         let uu____3131 = project i x  in
                                         let uu____3134 = project i y  in
                                         mk_stronger t2 uu____3131 uu____3134)
                                args
                               in
                            match uu____3093 with
                            | [] ->
                                failwith
                                  "Impossible: empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3082 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3188);
                                      FStar_Syntax_Syntax.pos = uu____3189;
                                      FStar_Syntax_Syntax.vars = uu____3190;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3234  ->
                                   match uu____3234 with
                                   | (bv,q) ->
                                       let uu____3248 =
                                         let uu____3250 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3250  in
                                       FStar_Syntax_Syntax.gen_bv uu____3248
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3259 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3259) bvs
                             in
                          let body =
                            let uu____3261 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3264 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3261 uu____3264  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3273);
                                      FStar_Syntax_Syntax.pos = uu____3274;
                                      FStar_Syntax_Syntax.vars = uu____3275;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3319  ->
                                   match uu____3319 with
                                   | (bv,q) ->
                                       let uu____3333 =
                                         let uu____3335 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3335  in
                                       FStar_Syntax_Syntax.gen_bv uu____3333
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3344 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3344) bvs
                             in
                          let body =
                            let uu____3346 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3349 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3346 uu____3349  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3356 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3359 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3362 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3365 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3359 uu____3362 uu____3365  in
                    let uu____3368 =
                      let uu____3369 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3369  in
                    FStar_Syntax_Util.abs uu____3368 body ret_tot_type  in
                  let stronger1 =
                    let uu____3411 = mk_lid "stronger"  in
                    register env1 uu____3411 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3419 = FStar_Util.prefix gamma  in
                    match uu____3419 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3485 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3485
                             in
                          let uu____3490 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3490 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3500 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3500  in
                              let guard_free1 =
                                let uu____3512 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3512  in
                              let pat =
                                let uu____3516 =
                                  let uu____3527 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3527]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3516
                                 in
                              let pattern_guarded_body =
                                let uu____3555 =
                                  let uu____3556 =
                                    let uu____3563 =
                                      let uu____3564 =
                                        let uu____3585 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1
                                           in
                                        let uu____3590 =
                                          let uu____3603 =
                                            let uu____3614 =
                                              FStar_Syntax_Syntax.as_arg pat
                                               in
                                            [uu____3614]  in
                                          [uu____3603]  in
                                        (uu____3585, uu____3590)  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3564
                                       in
                                    (body, uu____3563)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3556  in
                                mk1 uu____3555  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3677 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3686 =
                            let uu____3689 =
                              let uu____3690 =
                                let uu____3693 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3696 =
                                  let uu____3707 = args_of_binders1 wp_args
                                     in
                                  let uu____3710 =
                                    let uu____3713 =
                                      let uu____3714 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3714
                                       in
                                    [uu____3713]  in
                                  FStar_List.append uu____3707 uu____3710  in
                                FStar_Syntax_Util.mk_app uu____3693
                                  uu____3696
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3690  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3689
                             in
                          FStar_Syntax_Util.abs gamma uu____3686
                            ret_gtot_type
                           in
                        let uu____3715 =
                          let uu____3716 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3716  in
                        FStar_Syntax_Util.abs uu____3715 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3732 = mk_lid "ite_wp"  in
                    register env1 uu____3732 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3740 = FStar_Util.prefix gamma  in
                    match uu____3740 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3798 =
                            let uu____3799 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3806 =
                              let uu____3817 =
                                let uu____3826 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3826  in
                              [uu____3817]  in
                            FStar_Syntax_Util.mk_app uu____3799 uu____3806
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3798
                           in
                        let uu____3843 =
                          let uu____3844 =
                            let uu____3853 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3853 gamma  in
                          FStar_List.append binders uu____3844  in
                        FStar_Syntax_Util.abs uu____3843 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3875 = mk_lid "null_wp"  in
                    register env1 uu____3875 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3888 =
                        let uu____3899 =
                          let uu____3902 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3903 =
                            let uu____3906 =
                              let uu____3907 =
                                let uu____3918 =
                                  let uu____3927 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3927  in
                                [uu____3918]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3907
                               in
                            let uu____3944 =
                              let uu____3947 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3947]  in
                            uu____3906 :: uu____3944  in
                          uu____3902 :: uu____3903  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3899
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3888  in
                    let uu____3956 =
                      let uu____3957 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3957  in
                    FStar_Syntax_Util.abs uu____3956 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3973 = mk_lid "wp_trivial"  in
                    register env1 uu____3973 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3979 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3979
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let ed_combs =
                      match ed.FStar_Syntax_Syntax.combinators with
                      | FStar_Syntax_Syntax.DM4F_eff combs ->
                          let uu____3993 =
                            let uu___340_3994 = combs  in
                            let uu____3995 =
                              let uu____3996 = c stronger2  in
                              ([], uu____3996)  in
                            let uu____4003 =
                              let uu____4004 = c wp_if_then_else2  in
                              ([], uu____4004)  in
                            let uu____4011 =
                              let uu____4012 = c ite_wp2  in ([], uu____4012)
                               in
                            let uu____4019 =
                              let uu____4020 = c wp_close2  in
                              ([], uu____4020)  in
                            let uu____4027 =
                              let uu____4028 = c wp_trivial2  in
                              ([], uu____4028)  in
                            {
                              FStar_Syntax_Syntax.ret_wp =
                                (uu___340_3994.FStar_Syntax_Syntax.ret_wp);
                              FStar_Syntax_Syntax.bind_wp =
                                (uu___340_3994.FStar_Syntax_Syntax.bind_wp);
                              FStar_Syntax_Syntax.stronger = uu____3995;
                              FStar_Syntax_Syntax.if_then_else = uu____4003;
                              FStar_Syntax_Syntax.ite_wp = uu____4011;
                              FStar_Syntax_Syntax.close_wp = uu____4019;
                              FStar_Syntax_Syntax.trivial = uu____4027;
                              FStar_Syntax_Syntax.repr =
                                (uu___340_3994.FStar_Syntax_Syntax.repr);
                              FStar_Syntax_Syntax.return_repr =
                                (uu___340_3994.FStar_Syntax_Syntax.return_repr);
                              FStar_Syntax_Syntax.bind_repr =
                                (uu___340_3994.FStar_Syntax_Syntax.bind_repr)
                            }  in
                          FStar_Syntax_Syntax.DM4F_eff uu____3993
                      | uu____4035 ->
                          failwith
                            "Impossible! For a DM4F effect combinators must be in DM4f_eff"
                       in
                    let uu____4037 =
                      let uu____4038 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4038  in
                    (uu____4037,
                      (let uu___344_4065 = ed  in
                       {
                         FStar_Syntax_Syntax.mname =
                           (uu___344_4065.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___344_4065.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.univs =
                           (uu___344_4065.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___344_4065.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature =
                           (uu___344_4065.FStar_Syntax_Syntax.signature);
                         FStar_Syntax_Syntax.combinators = ed_combs;
                         FStar_Syntax_Syntax.actions =
                           (uu___344_4065.FStar_Syntax_Syntax.actions);
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___344_4065.FStar_Syntax_Syntax.eff_attrs)
                       }))))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___349_4083 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___349_4083.subst);
        tc_const = (uu___349_4083.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4104 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4123 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4143) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4157  ->
                match uu___0_4157 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4160 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4162 ->
        let uu____4163 =
          let uu____4169 =
            let uu____4171 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4171
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4169)  in
        FStar_Errors.raise_error uu____4163 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4181  ->
    match uu___1_4181 with
    | N t ->
        let uu____4184 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4184
    | M t ->
        let uu____4188 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4188
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4197,c) -> nm_of_comp c
    | uu____4219 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4232 = nm_of_comp c  in
    match uu____4232 with | M uu____4234 -> true | N uu____4236 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4247 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4263 =
        let uu____4272 =
          let uu____4279 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4279  in
        [uu____4272]  in
      let uu____4298 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4263 uu____4298  in
    let uu____4301 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4301
  
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
        let uu____4343 =
          let uu____4344 =
            let uu____4359 =
              let uu____4368 =
                let uu____4375 =
                  let uu____4376 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4376  in
                let uu____4377 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4375, uu____4377)  in
              [uu____4368]  in
            let uu____4395 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4359, uu____4395)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4344  in
        mk1 uu____4343

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4435) ->
          let binders1 =
            FStar_List.map
              (fun uu____4481  ->
                 match uu____4481 with
                 | (bv,aqual) ->
                     let uu____4500 =
                       let uu___399_4501 = bv  in
                       let uu____4502 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___399_4501.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___399_4501.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4502
                       }  in
                     (uu____4500, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4507,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4509);
                             FStar_Syntax_Syntax.pos = uu____4510;
                             FStar_Syntax_Syntax.vars = uu____4511;_})
               ->
               let uu____4540 =
                 let uu____4541 =
                   let uu____4556 =
                     let uu____4559 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4559  in
                   (binders1, uu____4556)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4541  in
               mk1 uu____4540
           | uu____4570 ->
               let uu____4571 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4571 with
                | N hn ->
                    let uu____4573 =
                      let uu____4574 =
                        let uu____4589 =
                          let uu____4592 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4592  in
                        (binders1, uu____4589)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4574  in
                    mk1 uu____4573
                | M a ->
                    let uu____4604 =
                      let uu____4605 =
                        let uu____4620 =
                          let uu____4629 =
                            let uu____4638 =
                              let uu____4645 =
                                let uu____4646 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4646  in
                              let uu____4647 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4645, uu____4647)  in
                            [uu____4638]  in
                          FStar_List.append binders1 uu____4629  in
                        let uu____4671 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4620, uu____4671)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4605  in
                    mk1 uu____4604))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4765 = f x  in
                    FStar_Util.string_builder_append strb uu____4765);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4774 = f x1  in
                         FStar_Util.string_builder_append strb uu____4774))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4778 =
              let uu____4784 =
                let uu____4786 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4788 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4786 uu____4788
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4784)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4778  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4810 =
              let uu____4811 = FStar_Syntax_Subst.compress ty  in
              uu____4811.FStar_Syntax_Syntax.n  in
            match uu____4810 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4837 =
                  let uu____4839 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4839  in
                if uu____4837
                then false
                else
                  (try
                     (fun uu___448_4856  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4880 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4880 s  in
                              let uu____4883 =
                                let uu____4885 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4885  in
                              if uu____4883
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4891 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4891 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4916  ->
                                          match uu____4916 with
                                          | (bv,uu____4928) ->
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
            | uu____4956 ->
                ((let uu____4958 =
                    let uu____4964 =
                      let uu____4966 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4966
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4964)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4958);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4982 =
              let uu____4983 = FStar_Syntax_Subst.compress head2  in
              uu____4983.FStar_Syntax_Syntax.n  in
            match uu____4982 with
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
                  (let uu____4989 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4989)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4992 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4992 with
                 | ((uu____5002,ty),uu____5004) ->
                     let uu____5009 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5009
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5022 =
                         let uu____5023 = FStar_Syntax_Subst.compress res  in
                         uu____5023.FStar_Syntax_Syntax.n  in
                       (match uu____5022 with
                        | FStar_Syntax_Syntax.Tm_app uu____5027 -> true
                        | uu____5045 ->
                            ((let uu____5047 =
                                let uu____5053 =
                                  let uu____5055 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5055
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5053)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5047);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5063 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5065 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5068) ->
                is_valid_application t2
            | uu____5073 -> false  in
          let uu____5075 = is_valid_application head1  in
          if uu____5075
          then
            let uu____5078 =
              let uu____5079 =
                let uu____5096 =
                  FStar_List.map
                    (fun uu____5125  ->
                       match uu____5125 with
                       | (t2,qual) ->
                           let uu____5150 = star_type' env t2  in
                           (uu____5150, qual)) args
                   in
                (head1, uu____5096)  in
              FStar_Syntax_Syntax.Tm_app uu____5079  in
            mk1 uu____5078
          else
            (let uu____5167 =
               let uu____5173 =
                 let uu____5175 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5175
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5173)  in
             FStar_Errors.raise_err uu____5167)
      | FStar_Syntax_Syntax.Tm_bvar uu____5179 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5180 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5181 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5182 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5210 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5210 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___520_5218 = env  in
                 let uu____5219 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5219;
                   subst = (uu___520_5218.subst);
                   tc_const = (uu___520_5218.tc_const)
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
               ((let uu___535_5246 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___535_5246.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___535_5246.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5253 =
            let uu____5254 =
              let uu____5261 = star_type' env t2  in (uu____5261, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5254  in
          mk1 uu____5253
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5313 =
            let uu____5314 =
              let uu____5341 = star_type' env e  in
              let uu____5344 =
                let uu____5361 =
                  let uu____5370 = star_type' env t2  in
                  FStar_Util.Inl uu____5370  in
                (uu____5361, FStar_Pervasives_Native.None)  in
              (uu____5341, uu____5344, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5314  in
          mk1 uu____5313
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5458 =
            let uu____5459 =
              let uu____5486 = star_type' env e  in
              let uu____5489 =
                let uu____5506 =
                  let uu____5515 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5515  in
                (uu____5506, FStar_Pervasives_Native.None)  in
              (uu____5486, uu____5489, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5459  in
          mk1 uu____5458
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5556,(uu____5557,FStar_Pervasives_Native.Some uu____5558),uu____5559)
          ->
          let uu____5608 =
            let uu____5614 =
              let uu____5616 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5616
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5614)  in
          FStar_Errors.raise_err uu____5608
      | FStar_Syntax_Syntax.Tm_refine uu____5620 ->
          let uu____5627 =
            let uu____5633 =
              let uu____5635 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5635
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5633)  in
          FStar_Errors.raise_err uu____5627
      | FStar_Syntax_Syntax.Tm_uinst uu____5639 ->
          let uu____5646 =
            let uu____5652 =
              let uu____5654 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5654
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5652)  in
          FStar_Errors.raise_err uu____5646
      | FStar_Syntax_Syntax.Tm_quoted uu____5658 ->
          let uu____5665 =
            let uu____5671 =
              let uu____5673 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5673
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5671)  in
          FStar_Errors.raise_err uu____5665
      | FStar_Syntax_Syntax.Tm_constant uu____5677 ->
          let uu____5678 =
            let uu____5684 =
              let uu____5686 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5686
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5684)  in
          FStar_Errors.raise_err uu____5678
      | FStar_Syntax_Syntax.Tm_match uu____5690 ->
          let uu____5713 =
            let uu____5719 =
              let uu____5721 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5721
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5719)  in
          FStar_Errors.raise_err uu____5713
      | FStar_Syntax_Syntax.Tm_let uu____5725 ->
          let uu____5739 =
            let uu____5745 =
              let uu____5747 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5747
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5745)  in
          FStar_Errors.raise_err uu____5739
      | FStar_Syntax_Syntax.Tm_uvar uu____5751 ->
          let uu____5764 =
            let uu____5770 =
              let uu____5772 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5772
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5770)  in
          FStar_Errors.raise_err uu____5764
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5776 =
            let uu____5782 =
              let uu____5784 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5784
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5782)  in
          FStar_Errors.raise_err uu____5776
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5789 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5789
      | FStar_Syntax_Syntax.Tm_delayed uu____5792 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_5816  ->
    match uu___3_5816 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_5827  ->
                match uu___2_5827 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5830 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5840 =
      let uu____5841 = FStar_Syntax_Subst.compress t  in
      uu____5841.FStar_Syntax_Syntax.n  in
    match uu____5840 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5873 =
            let uu____5874 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5874  in
          is_C uu____5873  in
        if r
        then
          ((let uu____5898 =
              let uu____5900 =
                FStar_List.for_all
                  (fun uu____5911  ->
                     match uu____5911 with | (h,uu____5920) -> is_C h) args
                 in
              Prims.op_Negation uu____5900  in
            if uu____5898
            then
              let uu____5926 =
                let uu____5932 =
                  let uu____5934 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not a C-type (A * C): %s" uu____5934
                   in
                (FStar_Errors.Error_UnexpectedDM4FType, uu____5932)  in
              FStar_Errors.raise_error uu____5926 t.FStar_Syntax_Syntax.pos
            else ());
           true)
        else
          ((let uu____5944 =
              let uu____5946 =
                FStar_List.for_all
                  (fun uu____5958  ->
                     match uu____5958 with
                     | (h,uu____5967) ->
                         let uu____5972 = is_C h  in
                         Prims.op_Negation uu____5972) args
                 in
              Prims.op_Negation uu____5946  in
            if uu____5944
            then
              let uu____5975 =
                let uu____5981 =
                  let uu____5983 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not a C-type (C * A): %s" uu____5983
                   in
                (FStar_Errors.Error_UnexpectedDM4FType, uu____5981)  in
              FStar_Errors.raise_error uu____5975 t.FStar_Syntax_Syntax.pos
            else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6012 = nm_of_comp comp  in
        (match uu____6012 with
         | M t1 ->
             ((let uu____6016 = is_C t1  in
               if uu____6016
               then
                 let uu____6019 =
                   let uu____6025 =
                     let uu____6027 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not a C-type (C -> C): %s"
                       uu____6027
                      in
                   (FStar_Errors.Error_UnexpectedDM4FType, uu____6025)  in
                 FStar_Errors.raise_error uu____6019
                   t1.FStar_Syntax_Syntax.pos
               else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6036) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6042) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6048,uu____6049) -> is_C t1
    | uu____6090 -> false
  
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
          let uu____6126 =
            let uu____6127 =
              let uu____6144 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6147 =
                let uu____6158 =
                  let uu____6167 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6167)  in
                [uu____6158]  in
              (uu____6144, uu____6147)  in
            FStar_Syntax_Syntax.Tm_app uu____6127  in
          mk1 uu____6126  in
        let uu____6203 =
          let uu____6204 = FStar_Syntax_Syntax.mk_binder p  in [uu____6204]
           in
        FStar_Syntax_Util.abs uu____6203 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6229  ->
    match uu___4_6229 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6232 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6470 =
          match uu____6470 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6507 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6510 =
                       let uu____6512 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6512  in
                     Prims.op_Negation uu____6510)
                   in
                if uu____6507
                then
                  let uu____6514 =
                    let uu____6520 =
                      let uu____6522 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6524 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6526 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6522 uu____6524 uu____6526
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6520)  in
                  FStar_Errors.raise_err uu____6514
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6551 = mk_return env t1 s_e  in
                     ((M t1), uu____6551, u_e)))
               | (M t1,N t2) ->
                   let uu____6558 =
                     let uu____6564 =
                       let uu____6566 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6568 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6570 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6566 uu____6568 uu____6570
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6564)
                      in
                   FStar_Errors.raise_err uu____6558)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_6622 =
            match uu___5_6622 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6638 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6659 =
                let uu____6665 =
                  let uu____6667 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6667
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6665)  in
              FStar_Errors.raise_error uu____6659 e2.FStar_Syntax_Syntax.pos
          | M uu____6677 ->
              let uu____6678 = check env1 e2 context_nm  in
              strip_m uu____6678
           in
        let uu____6685 =
          let uu____6686 = FStar_Syntax_Subst.compress e  in
          uu____6686.FStar_Syntax_Syntax.n  in
        match uu____6685 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6695 ->
            let uu____6696 = infer env e  in return_if uu____6696
        | FStar_Syntax_Syntax.Tm_name uu____6703 ->
            let uu____6704 = infer env e  in return_if uu____6704
        | FStar_Syntax_Syntax.Tm_fvar uu____6711 ->
            let uu____6712 = infer env e  in return_if uu____6712
        | FStar_Syntax_Syntax.Tm_abs uu____6719 ->
            let uu____6738 = infer env e  in return_if uu____6738
        | FStar_Syntax_Syntax.Tm_constant uu____6745 ->
            let uu____6746 = infer env e  in return_if uu____6746
        | FStar_Syntax_Syntax.Tm_quoted uu____6753 ->
            let uu____6760 = infer env e  in return_if uu____6760
        | FStar_Syntax_Syntax.Tm_app uu____6767 ->
            let uu____6784 = infer env e  in return_if uu____6784
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6792 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6792 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6857) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6863) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6869,uu____6870) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6911 ->
            let uu____6925 =
              let uu____6927 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6927  in
            failwith uu____6925
        | FStar_Syntax_Syntax.Tm_type uu____6936 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6944 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6966 ->
            let uu____6973 =
              let uu____6975 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6975  in
            failwith uu____6973
        | FStar_Syntax_Syntax.Tm_uvar uu____6984 ->
            let uu____6997 =
              let uu____6999 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6999  in
            failwith uu____6997
        | FStar_Syntax_Syntax.Tm_delayed uu____7008 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7030 =
              let uu____7032 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7032  in
            failwith uu____7030

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
      let uu____7062 =
        let uu____7063 = FStar_Syntax_Subst.compress e  in
        uu____7063.FStar_Syntax_Syntax.n  in
      match uu____7062 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7082 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7082
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7133;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7134;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7140 =
                  let uu___770_7141 = rc  in
                  let uu____7142 =
                    let uu____7147 =
                      let uu____7150 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7150  in
                    FStar_Pervasives_Native.Some uu____7147  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___770_7141.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7142;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___770_7141.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7140
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___776_7162 = env  in
            let uu____7163 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7163;
              subst = (uu___776_7162.subst);
              tc_const = (uu___776_7162.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7189  ->
                 match uu____7189 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___783_7212 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___783_7212.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___783_7212.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7213 =
            FStar_List.fold_left
              (fun uu____7244  ->
                 fun uu____7245  ->
                   match (uu____7244, uu____7245) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7303 = is_C c  in
                       if uu____7303
                       then
                         let xw =
                           let uu____7313 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7313
                            in
                         let x =
                           let uu___795_7316 = bv  in
                           let uu____7317 =
                             let uu____7320 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7320  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___795_7316.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___795_7316.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7317
                           }  in
                         let env3 =
                           let uu___798_7322 = env2  in
                           let uu____7323 =
                             let uu____7326 =
                               let uu____7327 =
                                 let uu____7334 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7334)  in
                               FStar_Syntax_Syntax.NT uu____7327  in
                             uu____7326 :: (env2.subst)  in
                           {
                             tcenv = (uu___798_7322.tcenv);
                             subst = uu____7323;
                             tc_const = (uu___798_7322.tc_const)
                           }  in
                         let uu____7339 =
                           let uu____7342 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7343 =
                             let uu____7346 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7346 :: acc  in
                           uu____7342 :: uu____7343  in
                         (env3, uu____7339)
                       else
                         (let x =
                            let uu___801_7352 = bv  in
                            let uu____7353 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___801_7352.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___801_7352.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7353
                            }  in
                          let uu____7356 =
                            let uu____7359 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7359 :: acc  in
                          (env2, uu____7356))) (env1, []) binders1
             in
          (match uu____7213 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7379 =
                 let check_what =
                   let uu____7405 = is_monadic rc_opt1  in
                   if uu____7405 then check_m else check_n  in
                 let uu____7422 = check_what env2 body1  in
                 match uu____7422 with
                 | (t,s_body,u_body) ->
                     let uu____7442 =
                       let uu____7445 =
                         let uu____7446 = is_monadic rc_opt1  in
                         if uu____7446 then M t else N t  in
                       comp_of_nm uu____7445  in
                     (uu____7442, s_body, u_body)
                  in
               (match uu____7379 with
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
                                 let uu____7486 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7492  ->
                                           match uu___6_7492 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7495 -> false))
                                    in
                                 if uu____7486
                                 then
                                   let uu____7498 =
                                     FStar_List.filter
                                       (fun uu___7_7502  ->
                                          match uu___7_7502 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7505 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7498
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7516 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7522  ->
                                         match uu___8_7522 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7525 -> false))
                                  in
                               if uu____7516
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7534  ->
                                        match uu___9_7534 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7537 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7539 =
                                   let uu____7540 =
                                     let uu____7545 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7545
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7540 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7539
                               else
                                 (let uu____7552 =
                                    let uu___842_7553 = rc  in
                                    let uu____7554 =
                                      let uu____7559 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7559
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___842_7553.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7554;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___842_7553.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7552))
                       in
                    let uu____7564 =
                      let comp1 =
                        let uu____7572 = is_monadic rc_opt1  in
                        let uu____7574 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7572 uu____7574
                         in
                      let uu____7575 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7575,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7564 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7613 =
                             let uu____7614 =
                               let uu____7633 =
                                 let uu____7636 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7636 s_rc_opt  in
                               (s_binders1, s_body1, uu____7633)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7614  in
                           mk1 uu____7613  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7656 =
                             let uu____7657 =
                               let uu____7676 =
                                 let uu____7679 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7679 u_rc_opt  in
                               (u_binders2, u_body2, uu____7676)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7657  in
                           mk1 uu____7656  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7695;_};
            FStar_Syntax_Syntax.fv_delta = uu____7696;
            FStar_Syntax_Syntax.fv_qual = uu____7697;_}
          ->
          let uu____7700 =
            let uu____7705 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7705  in
          (match uu____7700 with
           | (uu____7736,t) ->
               let uu____7738 =
                 let uu____7739 = normalize1 t  in N uu____7739  in
               (uu____7738, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7740;
             FStar_Syntax_Syntax.vars = uu____7741;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7820 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7820 with
           | (unary_op1,uu____7844) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7915;
             FStar_Syntax_Syntax.vars = uu____7916;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8012 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8012 with
           | (unary_op1,uu____8036) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8115;
             FStar_Syntax_Syntax.vars = uu____8116;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8154 = infer env a  in
          (match uu____8154 with
           | (t,s,u) ->
               let uu____8170 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8170 with
                | (head1,uu____8194) ->
                    let uu____8219 =
                      let uu____8220 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8220  in
                    let uu____8221 =
                      let uu____8222 =
                        let uu____8223 =
                          let uu____8240 =
                            let uu____8251 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8251]  in
                          (head1, uu____8240)  in
                        FStar_Syntax_Syntax.Tm_app uu____8223  in
                      mk1 uu____8222  in
                    let uu____8288 =
                      let uu____8289 =
                        let uu____8290 =
                          let uu____8307 =
                            let uu____8318 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8318]  in
                          (head1, uu____8307)  in
                        FStar_Syntax_Syntax.Tm_app uu____8290  in
                      mk1 uu____8289  in
                    (uu____8219, uu____8221, uu____8288)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8355;
             FStar_Syntax_Syntax.vars = uu____8356;_},(a1,uu____8358)::a2::[])
          ->
          let uu____8414 = infer env a1  in
          (match uu____8414 with
           | (t,s,u) ->
               let uu____8430 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8430 with
                | (head1,uu____8454) ->
                    let uu____8479 =
                      let uu____8480 =
                        let uu____8481 =
                          let uu____8498 =
                            let uu____8509 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8509; a2]  in
                          (head1, uu____8498)  in
                        FStar_Syntax_Syntax.Tm_app uu____8481  in
                      mk1 uu____8480  in
                    let uu____8554 =
                      let uu____8555 =
                        let uu____8556 =
                          let uu____8573 =
                            let uu____8584 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8584; a2]  in
                          (head1, uu____8573)  in
                        FStar_Syntax_Syntax.Tm_app uu____8556  in
                      mk1 uu____8555  in
                    (t, uu____8479, uu____8554)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8629;
             FStar_Syntax_Syntax.vars = uu____8630;_},uu____8631)
          ->
          let uu____8656 =
            let uu____8662 =
              let uu____8664 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8664
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8662)  in
          FStar_Errors.raise_error uu____8656 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8674;
             FStar_Syntax_Syntax.vars = uu____8675;_},uu____8676)
          ->
          let uu____8701 =
            let uu____8707 =
              let uu____8709 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8709
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8707)  in
          FStar_Errors.raise_error uu____8701 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8745 = check_n env head1  in
          (match uu____8745 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8768 =
                   let uu____8769 = FStar_Syntax_Subst.compress t  in
                   uu____8769.FStar_Syntax_Syntax.n  in
                 match uu____8768 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8773 -> true
                 | uu____8789 -> false  in
               let rec flatten1 t =
                 let uu____8811 =
                   let uu____8812 = FStar_Syntax_Subst.compress t  in
                   uu____8812.FStar_Syntax_Syntax.n  in
                 match uu____8811 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8831);
                                FStar_Syntax_Syntax.pos = uu____8832;
                                FStar_Syntax_Syntax.vars = uu____8833;_})
                     when is_arrow t1 ->
                     let uu____8862 = flatten1 t1  in
                     (match uu____8862 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8962,uu____8963)
                     -> flatten1 e1
                 | uu____9004 ->
                     let uu____9005 =
                       let uu____9011 =
                         let uu____9013 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9013
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9011)  in
                     FStar_Errors.raise_err uu____9005
                  in
               let uu____9031 = flatten1 t_head  in
               (match uu____9031 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9106 =
                          let uu____9112 =
                            let uu____9114 = FStar_Util.string_of_int n1  in
                            let uu____9116 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9118 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9114 uu____9116 uu____9118
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9112)
                           in
                        FStar_Errors.raise_err uu____9106)
                     else ();
                     (let uu____9124 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9124 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9177 args1 =
                            match uu____9177 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9277 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9277
                                 | (binders3,[]) ->
                                     let uu____9315 =
                                       let uu____9316 =
                                         let uu____9319 =
                                           let uu____9320 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9320
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9319
                                          in
                                       uu____9316.FStar_Syntax_Syntax.n  in
                                     (match uu____9315 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9353 =
                                            let uu____9354 =
                                              let uu____9355 =
                                                let uu____9370 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9370)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9355
                                               in
                                            mk1 uu____9354  in
                                          N uu____9353
                                      | uu____9383 -> failwith "wat?")
                                 | ([],uu____9385::uu____9386) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9439)::binders3,(arg,uu____9442)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9529 = FStar_List.splitAt n' binders1  in
                          (match uu____9529 with
                           | (binders2,uu____9563) ->
                               let uu____9596 =
                                 let uu____9619 =
                                   FStar_List.map2
                                     (fun uu____9681  ->
                                        fun uu____9682  ->
                                          match (uu____9681, uu____9682) with
                                          | ((bv,uu____9730),(arg,q)) ->
                                              let uu____9759 =
                                                let uu____9760 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9760.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9759 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9781 ->
                                                   let uu____9782 =
                                                     let uu____9789 =
                                                       star_type' env arg  in
                                                     (uu____9789, q)  in
                                                   (uu____9782, [(arg, q)])
                                               | uu____9826 ->
                                                   let uu____9827 =
                                                     check_n env arg  in
                                                   (match uu____9827 with
                                                    | (uu____9852,s_arg,u_arg)
                                                        ->
                                                        let uu____9855 =
                                                          let uu____9864 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9864
                                                          then
                                                            let uu____9875 =
                                                              let uu____9882
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9882, q)
                                                               in
                                                            [uu____9875;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9855))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9619  in
                               (match uu____9596 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10010 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10023 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10010, uu____10023)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10092) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10098) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10104,uu____10105) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10147 =
            let uu____10148 = env.tc_const c  in N uu____10148  in
          (uu____10147, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10155 ->
          let uu____10169 =
            let uu____10171 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10171  in
          failwith uu____10169
      | FStar_Syntax_Syntax.Tm_type uu____10180 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10188 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10210 ->
          let uu____10217 =
            let uu____10219 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10219  in
          failwith uu____10217
      | FStar_Syntax_Syntax.Tm_uvar uu____10228 ->
          let uu____10241 =
            let uu____10243 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10243  in
          failwith uu____10241
      | FStar_Syntax_Syntax.Tm_delayed uu____10252 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10274 =
            let uu____10276 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10276  in
          failwith uu____10274

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
          let uu____10325 = check_n env e0  in
          match uu____10325 with
          | (uu____10338,s_e0,u_e0) ->
              let uu____10341 =
                let uu____10370 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10431 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10431 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1117_10473 = env  in
                             let uu____10474 =
                               let uu____10475 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10475
                                in
                             {
                               tcenv = uu____10474;
                               subst = (uu___1117_10473.subst);
                               tc_const = (uu___1117_10473.tc_const)
                             }  in
                           let uu____10478 = f env1 body  in
                           (match uu____10478 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10550 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10370  in
              (match uu____10341 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10656 = FStar_List.hd nms  in
                     match uu____10656 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10665  ->
                          match uu___10_10665 with
                          | M uu____10667 -> true
                          | uu____10669 -> false) nms
                      in
                   let uu____10671 =
                     let uu____10708 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10798  ->
                              match uu____10798 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____10982 =
                                         check env original_body (M t2)  in
                                       (match uu____10982 with
                                        | (uu____11019,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11058,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10708  in
                   (match uu____10671 with
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
                              (fun uu____11247  ->
                                 match uu____11247 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11298 =
                                         let uu____11299 =
                                           let uu____11316 =
                                             let uu____11327 =
                                               let uu____11336 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11339 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11336, uu____11339)  in
                                             [uu____11327]  in
                                           (s_body, uu____11316)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11299
                                          in
                                       mk1 uu____11298  in
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
                            let uu____11474 =
                              let uu____11475 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11475]  in
                            let uu____11494 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11474 uu____11494
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11518 =
                              let uu____11527 =
                                let uu____11534 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11534
                                 in
                              [uu____11527]  in
                            let uu____11553 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11518 uu____11553
                             in
                          let uu____11556 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11595 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11556, uu____11595)
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
                           let uu____11705 =
                             let uu____11706 =
                               let uu____11707 =
                                 let uu____11734 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11734,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11707
                                in
                             mk1 uu____11706  in
                           let uu____11793 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11705, uu____11793))))

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
              let uu____11858 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11858]  in
            let uu____11877 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11877 with
            | (x_binders1,e21) ->
                let uu____11890 = infer env e1  in
                (match uu____11890 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____11907 = is_C t1  in
                       if uu____11907
                       then
                         let uu___1203_11910 = binding  in
                         let uu____11911 =
                           let uu____11914 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____11914  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1203_11910.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1203_11910.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11911;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1203_11910.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1203_11910.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1203_11910.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1203_11910.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1206_11918 = env  in
                       let uu____11919 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1208_11921 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1208_11921.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1208_11921.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11919;
                         subst = (uu___1206_11918.subst);
                         tc_const = (uu___1206_11918.tc_const)
                       }  in
                     let uu____11922 = proceed env1 e21  in
                     (match uu____11922 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1215_11939 = binding  in
                            let uu____11940 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1215_11939.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1215_11939.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11940;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1215_11939.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1215_11939.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1215_11939.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1215_11939.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____11943 =
                            let uu____11944 =
                              let uu____11945 =
                                let uu____11959 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1218_11976 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1218_11976.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1218_11976.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1218_11976.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1218_11976.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1218_11976.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1218_11976.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11959)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11945  in
                            mk1 uu____11944  in
                          let uu____11977 =
                            let uu____11978 =
                              let uu____11979 =
                                let uu____11993 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1220_12010 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1220_12010.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1220_12010.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1220_12010.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1220_12010.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1220_12010.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1220_12010.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11993)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11979  in
                            mk1 uu____11978  in
                          (nm_rec, uu____11943, uu____11977))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1227_12015 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1227_12015.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1227_12015.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1227_12015.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1227_12015.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1227_12015.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1230_12017 = env  in
                       let uu____12018 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1232_12020 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1232_12020.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1232_12020.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12018;
                         subst = (uu___1230_12017.subst);
                         tc_const = (uu___1230_12017.tc_const)
                       }  in
                     let uu____12021 = ensure_m env1 e21  in
                     (match uu____12021 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12045 =
                              let uu____12046 =
                                let uu____12063 =
                                  let uu____12074 =
                                    let uu____12083 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12086 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12083, uu____12086)  in
                                  [uu____12074]  in
                                (s_e2, uu____12063)  in
                              FStar_Syntax_Syntax.Tm_app uu____12046  in
                            mk1 uu____12045  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12128 =
                              let uu____12129 =
                                let uu____12146 =
                                  let uu____12157 =
                                    let uu____12166 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12166)  in
                                  [uu____12157]  in
                                (s_e1, uu____12146)  in
                              FStar_Syntax_Syntax.Tm_app uu____12129  in
                            mk1 uu____12128  in
                          let uu____12202 =
                            let uu____12203 =
                              let uu____12204 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12204]  in
                            FStar_Syntax_Util.abs uu____12203 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12223 =
                            let uu____12224 =
                              let uu____12225 =
                                let uu____12239 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1244_12256 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1244_12256.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1244_12256.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1244_12256.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1244_12256.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1244_12256.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1244_12256.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12239)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12225  in
                            mk1 uu____12224  in
                          ((M t2), uu____12202, uu____12223)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12266 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12266  in
      let uu____12267 = check env e mn  in
      match uu____12267 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12283 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12306 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12306  in
      let uu____12307 = check env e mn  in
      match uu____12307 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12323 -> failwith "[check_m]: impossible"

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
        (let uu____12356 =
           let uu____12358 = is_C c  in Prims.op_Negation uu____12358  in
         if uu____12356
         then
           let uu____12361 =
             let uu____12367 =
               let uu____12369 = FStar_Syntax_Print.term_to_string c  in
               FStar_Util.format1 "Not a DM4F C-type: %s" uu____12369  in
             (FStar_Errors.Error_UnexpectedDM4FType, uu____12367)  in
           FStar_Errors.raise_error uu____12361 c.FStar_Syntax_Syntax.pos
         else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12383 =
           let uu____12384 = FStar_Syntax_Subst.compress c  in
           uu____12384.FStar_Syntax_Syntax.n  in
         match uu____12383 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12413 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12413 with
              | (wp_head,wp_args) ->
                  ((let uu____12457 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12476 =
                           let uu____12478 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12478
                            in
                         Prims.op_Negation uu____12476)
                       in
                    if uu____12457 then failwith "mismatch" else ());
                   (let uu____12491 =
                      let uu____12492 =
                        let uu____12509 =
                          FStar_List.map2
                            (fun uu____12547  ->
                               fun uu____12548  ->
                                 match (uu____12547, uu____12548) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12610 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12610
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12619 =
                                         let uu____12621 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12621 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12619
                                       then
                                         let uu____12623 =
                                           let uu____12629 =
                                             let uu____12631 =
                                               print_implicit q  in
                                             let uu____12633 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12631 uu____12633
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12629)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12623
                                       else ());
                                      (let uu____12639 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12639, q)))) args wp_args
                           in
                        (head1, uu____12509)  in
                      FStar_Syntax_Syntax.Tm_app uu____12492  in
                    mk1 uu____12491)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12685 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12685 with
              | (binders_orig,comp1) ->
                  let uu____12692 =
                    let uu____12709 =
                      FStar_List.map
                        (fun uu____12749  ->
                           match uu____12749 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12777 = is_C h  in
                               if uu____12777
                               then
                                 let w' =
                                   let uu____12793 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12793
                                    in
                                 let uu____12795 =
                                   let uu____12804 =
                                     let uu____12813 =
                                       let uu____12820 =
                                         let uu____12821 =
                                           let uu____12822 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12822  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12821
                                          in
                                       (uu____12820, q)  in
                                     [uu____12813]  in
                                   (w', q) :: uu____12804  in
                                 (w', uu____12795)
                               else
                                 (let x =
                                    let uu____12856 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____12856
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12709  in
                  (match uu____12692 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____12930 =
                           let uu____12933 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12933
                            in
                         FStar_Syntax_Subst.subst_comp uu____12930 comp1  in
                       let app =
                         let uu____12937 =
                           let uu____12938 =
                             let uu____12955 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____12974 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____12975 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12974, uu____12975)) bvs
                                in
                             (wp, uu____12955)  in
                           FStar_Syntax_Syntax.Tm_app uu____12938  in
                         mk1 uu____12937  in
                       let comp3 =
                         let uu____12990 = type_of_comp comp2  in
                         let uu____12991 = is_monadic_comp comp2  in
                         trans_G env uu____12990 uu____12991 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____12994,uu____12995) ->
             trans_F_ env e wp
         | uu____13036 -> failwith "impossible trans_F_")

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
            let uu____13044 =
              let uu____13045 = star_type' env h  in
              let uu____13048 =
                let uu____13059 =
                  let uu____13068 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13068)  in
                [uu____13059]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13045;
                FStar_Syntax_Syntax.effect_args = uu____13048;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13044
          else
            (let uu____13094 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13094)

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
    fun t  -> let uu____13115 = n env.tcenv t  in star_type' env uu____13115
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13135 = n env.tcenv t  in check_n env uu____13135
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13152 = n env.tcenv c  in
        let uu____13153 = n env.tcenv wp  in
        trans_F_ env uu____13152 uu____13153
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env  ->
      fun t  ->
        (let uu____13173 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____13173
         then
           let uu____13177 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s
             uu____13177
         else ());
        (let uu____13182 = FStar_TypeChecker_TcTerm.tc_term env t  in
         match uu____13182 with
         | (t',uu____13190,uu____13191) ->
             ((let uu____13193 =
                 FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                  in
               if uu____13193
               then
                 let uu____13197 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____13197
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
      let uu____13233 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature)
         in
      match uu____13233 with
      | (effect_binders_un,signature_un) ->
          let uu____13254 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____13254 with
           | (effect_binders,env1,uu____13273) ->
               let uu____13274 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____13274 with
                | (signature,uu____13290) ->
                    let raise_error1 uu____13306 =
                      match uu____13306 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____13342  ->
                           match uu____13342 with
                           | (bv,qual) ->
                               let uu____13361 =
                                 let uu___1370_13362 = bv  in
                                 let uu____13363 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1370_13362.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1370_13362.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____13363
                                 }  in
                               (uu____13361, qual)) effect_binders
                       in
                    let uu____13368 =
                      let uu____13375 =
                        let uu____13376 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____13376.FStar_Syntax_Syntax.n  in
                      match uu____13375 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____13386)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____13418 ->
                          raise_error1
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____13368 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____13444 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____13444
                           then
                             let uu____13447 =
                               let uu____13450 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____13450  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____13447
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env2 other_binders t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____13498 =
                             FStar_TypeChecker_TcTerm.tc_term env2 t1  in
                           match uu____13498 with
                           | (t2,comp,uu____13511) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x
                             FStar_Pervasives_Native.None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____13520 =
                           let uu____13525 =
                             let uu____13526 =
                               let uu____13535 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____13535
                                 FStar_Util.must
                                in
                             FStar_All.pipe_right uu____13526
                               FStar_Pervasives_Native.snd
                              in
                           open_and_check env1 [] uu____13525  in
                         (match uu____13520 with
                          | (repr,_comp) ->
                              ((let uu____13581 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____13581
                                then
                                  let uu____13585 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____13585
                                else ());
                               (let dmff_env =
                                  empty env1
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env1 FStar_Range.dummyRange)
                                   in
                                let wp_type = star_type dmff_env repr  in
                                let uu____13592 =
                                  recheck_debug "*" env1 wp_type  in
                                let wp_a =
                                  let uu____13595 =
                                    let uu____13596 =
                                      let uu____13597 =
                                        let uu____13614 =
                                          let uu____13625 =
                                            let uu____13634 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____13637 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____13634, uu____13637)  in
                                          [uu____13625]  in
                                        (wp_type, uu____13614)  in
                                      FStar_Syntax_Syntax.Tm_app uu____13597
                                       in
                                    mk1 uu____13596  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env1
                                    uu____13595
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____13685 =
                                      let uu____13692 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____13692)  in
                                    let uu____13698 =
                                      let uu____13707 =
                                        let uu____13714 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____13714
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____13707]  in
                                    uu____13685 :: uu____13698  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____13751 =
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
                                  let uu____13817 = item  in
                                  match uu____13817 with
                                  | (u_item,item1) ->
                                      let uu____13832 =
                                        open_and_check env2 other_binders
                                          item1
                                         in
                                      (match uu____13832 with
                                       | (item2,item_comp) ->
                                           ((let uu____13848 =
                                               let uu____13850 =
                                                 FStar_TypeChecker_Common.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____13850
                                                in
                                             if uu____13848
                                             then
                                               let uu____13853 =
                                                 let uu____13859 =
                                                   let uu____13861 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____13863 =
                                                     FStar_TypeChecker_Common.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____13861 uu____13863
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____13859)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____13853
                                             else ());
                                            (let uu____13869 =
                                               star_expr dmff_env1 item2  in
                                             match uu____13869 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____13887 =
                                                   recheck_debug "*" env2
                                                     item_wp
                                                    in
                                                 let uu____13889 =
                                                   recheck_debug "_" env2
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____13891 =
                                  let uu____13900 =
                                    let uu____13905 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____13905
                                      FStar_Util.must
                                     in
                                  elaborate_and_star dmff_env [] uu____13900
                                   in
                                match uu____13891 with
                                | (dmff_env1,uu____13933,bind_wp,bind_elab)
                                    ->
                                    let uu____13936 =
                                      let uu____13945 =
                                        let uu____13950 =
                                          FStar_All.pipe_right ed
                                            FStar_Syntax_Util.get_return_repr
                                           in
                                        FStar_All.pipe_right uu____13950
                                          FStar_Util.must
                                         in
                                      elaborate_and_star dmff_env1 []
                                        uu____13945
                                       in
                                    (match uu____13936 with
                                     | (dmff_env2,uu____13994,return_wp,return_elab)
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
                                           let uu____14003 =
                                             let uu____14004 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____14004.FStar_Syntax_Syntax.n
                                              in
                                           match uu____14003 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____14062 =
                                                 let uu____14081 =
                                                   let uu____14086 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____14086
                                                    in
                                                 match uu____14081 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____14168 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____14062 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____14222 =
                                                        get_env dmff_env2  in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____14222
                                                        [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____14245 =
                                                          let uu____14246 =
                                                            let uu____14263 =
                                                              let uu____14274
                                                                =
                                                                let uu____14283
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____14288
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____14283,
                                                                  uu____14288)
                                                                 in
                                                              [uu____14274]
                                                               in
                                                            (wp_type,
                                                              uu____14263)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____14246
                                                           in
                                                        mk1 uu____14245  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____14324 =
                                                      let uu____14333 =
                                                        let uu____14334 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____14334
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____14333
                                                       in
                                                    (match uu____14324 with
                                                     | (bs1,body2,what') ->
                                                         let fail1
                                                           uu____14357 =
                                                           let error_msg =
                                                             let uu____14360
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____14362
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
                                                               uu____14360
                                                               uu____14362
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
                                                               ((let uu____14372
                                                                   =
                                                                   let uu____14374
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____14374
                                                                    in
                                                                 if
                                                                   uu____14372
                                                                 then
                                                                   fail1 ()
                                                                 else ());
                                                                (let uu____14379
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
                                                                   uu____14379
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
                                                             let uu____14408
                                                               =
                                                               let uu____14413
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp
                                                                  in
                                                               let uu____14414
                                                                 =
                                                                 let uu____14415
                                                                   =
                                                                   let uu____14424
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'  in
                                                                   (uu____14424,
                                                                    FStar_Pervasives_Native.None)
                                                                    in
                                                                 [uu____14415]
                                                                  in
                                                               FStar_Syntax_Syntax.mk_Tm_app
                                                                 uu____14413
                                                                 uu____14414
                                                                in
                                                             uu____14408
                                                               FStar_Pervasives_Native.None
                                                               FStar_Range.dummyRange
                                                              in
                                                           let uu____14459 =
                                                             let uu____14460
                                                               =
                                                               let uu____14469
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____14469]
                                                                in
                                                             b11 ::
                                                               uu____14460
                                                              in
                                                           let uu____14494 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____14459
                                                             uu____14494
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____14497 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____14505 =
                                             let uu____14506 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____14506.FStar_Syntax_Syntax.n
                                              in
                                           match uu____14505 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____14564 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____14564
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____14585 ->
                                               raise_error1
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____14593 =
                                             let uu____14594 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____14594.FStar_Syntax_Syntax.n
                                              in
                                           match uu____14593 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____14628 =
                                                 let uu____14629 =
                                                   let uu____14638 =
                                                     let uu____14645 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____14645
                                                      in
                                                   [uu____14638]  in
                                                 FStar_List.append
                                                   uu____14629 binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____14628 body what
                                           | uu____14664 ->
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
                                             (let uu____14694 =
                                                let uu____14695 =
                                                  let uu____14696 =
                                                    let uu____14713 =
                                                      let uu____14724 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____14724
                                                       in
                                                    (t, uu____14713)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____14696
                                                   in
                                                mk1 uu____14695  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____14694)
                                            in
                                         let rec apply_last1 f l =
                                           match l with
                                           | [] ->
                                               failwith
                                                 "impossible: empty path.."
                                           | a2::[] ->
                                               let uu____14782 = f a2  in
                                               [uu____14782]
                                           | x::xs ->
                                               let uu____14793 =
                                                 apply_last1 f xs  in
                                               x :: uu____14793
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
                                           let uu____14827 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env1 l'
                                              in
                                           match uu____14827 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____14857 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____14857
                                                 then
                                                   let uu____14860 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____14860
                                                 else ());
                                                (let uu____14865 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____14865))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____14874 =
                                                 let uu____14879 =
                                                   mk_lid name  in
                                                 let uu____14880 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env1 uu____14879
                                                   uu____14880
                                                  in
                                               (match uu____14874 with
                                                | (sigelt,fv) ->
                                                    ((let uu____14884 =
                                                        let uu____14887 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt :: uu____14887
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____14884);
                                                     fv))
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____14941 =
                                             let uu____14944 =
                                               FStar_Syntax_Syntax.mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       (FStar_Pervasives_Native.Some
                                                          "--admit_smt_queries true")))
                                                in
                                             let uu____14947 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____14944 :: uu____14947  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____14941);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____14999 =
                                              let uu____15002 =
                                                FStar_Syntax_Syntax.mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____15003 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____15002 :: uu____15003  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____14999);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____15055 =
                                               let uu____15058 =
                                                 FStar_Syntax_Syntax.mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         (FStar_Pervasives_Native.Some
                                                            "--admit_smt_queries true")))
                                                  in
                                               let uu____15061 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____15058 :: uu____15061  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____15055);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____15113 =
                                                let uu____15116 =
                                                  FStar_Syntax_Syntax.mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____15117 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____15116 :: uu____15117
                                                 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____15113);
                                             (let uu____15166 =
                                                FStar_List.fold_left
                                                  (fun uu____15206  ->
                                                     fun action  ->
                                                       match uu____15206 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____15227 =
                                                             let uu____15234
                                                               =
                                                               get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____15234
                                                               params_un
                                                              in
                                                           (match uu____15227
                                                            with
                                                            | (action_params,env',uu____15243)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____15269
                                                                     ->
                                                                    match uu____15269
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____15288
                                                                    =
                                                                    let uu___1563_15289
                                                                    = bv  in
                                                                    let uu____15290
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___1563_15289.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1563_15289.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____15290
                                                                    }  in
                                                                    (uu____15288,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____15296
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____15296
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
                                                                    uu____15335
                                                                    ->
                                                                    let uu____15336
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____15336
                                                                     in
                                                                    ((
                                                                    let uu____15340
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____15340
                                                                    then
                                                                    let uu____15345
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____15348
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____15351
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____15353
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____15345
                                                                    uu____15348
                                                                    uu____15351
                                                                    uu____15353
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
                                                                    let uu____15362
                                                                    =
                                                                    let uu____15365
                                                                    =
                                                                    let uu___1585_15366
                                                                    = action
                                                                     in
                                                                    let uu____15367
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____15368
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1585_15366.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1585_15366.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___1585_15366.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____15367;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____15368
                                                                    }  in
                                                                    uu____15365
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____15362))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____15166 with
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
                                                      let uu____15412 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____15419 =
                                                        let uu____15428 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____15428]  in
                                                      uu____15412 ::
                                                        uu____15419
                                                       in
                                                    let uu____15453 =
                                                      let uu____15456 =
                                                        let uu____15457 =
                                                          let uu____15458 =
                                                            let uu____15475 =
                                                              let uu____15486
                                                                =
                                                                let uu____15495
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____15498
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____15495,
                                                                  uu____15498)
                                                                 in
                                                              [uu____15486]
                                                               in
                                                            (repr,
                                                              uu____15475)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____15458
                                                           in
                                                        mk1 uu____15457  in
                                                      let uu____15534 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      trans_F dmff_env3
                                                        uu____15456
                                                        uu____15534
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____15453
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____15535 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register "repr" repr1  in
                                                  let uu____15539 =
                                                    let uu____15548 =
                                                      let uu____15549 =
                                                        let uu____15552 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____15552
                                                         in
                                                      uu____15549.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____15548 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____15566)
                                                        ->
                                                        let uu____15603 =
                                                          let uu____15624 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____15624
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____15692 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____15603
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____15757
                                                               =
                                                               let uu____15758
                                                                 =
                                                                 let uu____15761
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____15761
                                                                  in
                                                               uu____15758.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____15757
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____15794
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____15794
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____15809
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____15840
                                                                     ->
                                                                    match uu____15840
                                                                    with
                                                                    | 
                                                                    (bv,uu____15849)
                                                                    ->
                                                                    let uu____15854
                                                                    =
                                                                    let uu____15856
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15856
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15854
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____15809
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
                                                                    let uu____15948
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____15948
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____15958
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____15969
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____15969
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____15979
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____15982
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____15979,
                                                                    uu____15982)))
                                                              | uu____15997
                                                                  ->
                                                                  let uu____15998
                                                                    =
                                                                    let uu____16004
                                                                    =
                                                                    let uu____16006
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____16006
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____16004)
                                                                     in
                                                                  raise_error1
                                                                    uu____15998))
                                                    | uu____16018 ->
                                                        let uu____16019 =
                                                          let uu____16025 =
                                                            let uu____16027 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____16027
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____16025)
                                                           in
                                                        raise_error1
                                                          uu____16019
                                                     in
                                                  (match uu____15539 with
                                                   | (pre,post) ->
                                                       ((let uu____16060 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____16063 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____16066 =
                                                           register "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed_combs =
                                                           match ed.FStar_Syntax_Syntax.combinators
                                                           with
                                                           | FStar_Syntax_Syntax.DM4F_eff
                                                               combs ->
                                                               let uu____16070
                                                                 =
                                                                 let uu___1643_16071
                                                                   = combs
                                                                    in
                                                                 let uu____16072
                                                                   =
                                                                   let uu____16073
                                                                    =
                                                                    apply_close
                                                                    return_wp2
                                                                     in
                                                                   ([],
                                                                    uu____16073)
                                                                    in
                                                                 let uu____16080
                                                                   =
                                                                   let uu____16081
                                                                    =
                                                                    apply_close
                                                                    bind_wp2
                                                                     in
                                                                   ([],
                                                                    uu____16081)
                                                                    in
                                                                 let uu____16088
                                                                   =
                                                                   let uu____16091
                                                                    =
                                                                    let uu____16092
                                                                    =
                                                                    apply_close
                                                                    repr2  in
                                                                    ([],
                                                                    uu____16092)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16091
                                                                    in
                                                                 let uu____16099
                                                                   =
                                                                   let uu____16102
                                                                    =
                                                                    let uu____16103
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                    ([],
                                                                    uu____16103)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16102
                                                                    in
                                                                 let uu____16110
                                                                   =
                                                                   let uu____16113
                                                                    =
                                                                    let uu____16114
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    ([],
                                                                    uu____16114)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16113
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.ret_wp
                                                                    =
                                                                    uu____16072;
                                                                   FStar_Syntax_Syntax.bind_wp
                                                                    =
                                                                    uu____16080;
                                                                   FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    (uu___1643_16071.FStar_Syntax_Syntax.stronger);
                                                                   FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    (uu___1643_16071.FStar_Syntax_Syntax.if_then_else);
                                                                   FStar_Syntax_Syntax.ite_wp
                                                                    =
                                                                    (uu___1643_16071.FStar_Syntax_Syntax.ite_wp);
                                                                   FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    (uu___1643_16071.FStar_Syntax_Syntax.close_wp);
                                                                   FStar_Syntax_Syntax.trivial
                                                                    =
                                                                    (uu___1643_16071.FStar_Syntax_Syntax.trivial);
                                                                   FStar_Syntax_Syntax.repr
                                                                    =
                                                                    uu____16088;
                                                                   FStar_Syntax_Syntax.return_repr
                                                                    =
                                                                    uu____16099;
                                                                   FStar_Syntax_Syntax.bind_repr
                                                                    =
                                                                    uu____16110
                                                                 }  in
                                                               FStar_Syntax_Syntax.DM4F_eff
                                                                 uu____16070
                                                           | uu____16121 ->
                                                               failwith
                                                                 "Impossible! For a DM4F effect combinators must be in DM4f_eff"
                                                            in
                                                         let ed1 =
                                                           let uu___1647_16124
                                                             = ed  in
                                                           let uu____16125 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____16126 =
                                                             let uu____16127
                                                               =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature
                                                                in
                                                             ([],
                                                               uu____16127)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___1647_16124.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___1647_16124.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___1647_16124.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____16125;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____16126;
                                                             FStar_Syntax_Syntax.combinators
                                                               = ed_combs;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___1647_16124.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____16134 =
                                                           gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____16134
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____16152
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____16152
                                                               then
                                                                 let uu____16156
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____16156
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
                                                                    let uu____16176
                                                                    =
                                                                    let uu____16179
                                                                    =
                                                                    let uu____16180
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____16180)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16179
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
                                                                    uu____16176;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____16187
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16187
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____16190
                                                                 =
                                                                 let uu____16193
                                                                   =
                                                                   let uu____16196
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____16196
                                                                    in
                                                                 FStar_List.append
                                                                   uu____16193
                                                                   sigelts'
                                                                  in
                                                               (uu____16190,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  