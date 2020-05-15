open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with | { tcenv; subst; tc_const;_} -> tcenv
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with | { tcenv; subst; tc_const;_} -> subst
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with | { tcenv; subst; tc_const;_} -> tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env1  -> fun tc_const  -> { tcenv = env1; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
  =
  fun env1  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env1 wp_a
               in
            let a1 =
              let uu___28_129 = a  in
              let uu____130 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env1
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
               FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED")
                in
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
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED")
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
              let mk x = FStar_Syntax_Syntax.mk x FStar_Range.dummyRange  in
              let sigelts = FStar_Util.mk_ref []  in
              let register env2 lident def =
                let uu____357 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env2 lident
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
              let binders_of_list =
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
              let args_of_binders =
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
                  let mk1 f =
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
                  let uu____641 = mk1 FStar_Syntax_Syntax.mk_Total  in
                  let uu____642 = mk1 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____641, uu____642)  in
                match uu____555 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env1 ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env1 gctx_lid gctx_def  in
                    let mk_app fv t =
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
                      mk uu____684  in
                    (env1, (mk_app ctx_fv), (mk_app gctx_fv))
                 in
              match uu____538 with
              | (env2,mk_ctx,mk_gctx) ->
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
                    let ret =
                      let uu____860 =
                        let uu____861 =
                          let uu____864 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____864  in
                        FStar_Syntax_Util.residual_tot uu____861  in
                      FStar_Pervasives_Native.Some uu____860  in
                    let body =
                      let uu____868 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____868 ret  in
                    let uu____871 =
                      let uu____872 = mk_all_implicit binders  in
                      let uu____879 =
                        binders_of_list [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____872 uu____879  in
                    FStar_Syntax_Util.abs uu____871 body ret  in
                  let c_pure1 =
                    let uu____917 = mk_lid "pure"  in
                    register env2 uu____917 c_pure  in
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
                    let ret =
                      let uu____971 =
                        let uu____972 =
                          let uu____975 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____975  in
                        FStar_Syntax_Util.residual_tot uu____972  in
                      FStar_Pervasives_Native.Some uu____971  in
                    let outer_body =
                      let gamma_as_args = args_of_binders gamma  in
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
                      FStar_Syntax_Util.abs gamma inner_body ret  in
                    let uu____1007 =
                      let uu____1008 = mk_all_implicit binders  in
                      let uu____1015 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____1008 uu____1015  in
                    FStar_Syntax_Util.abs uu____1007 outer_body ret  in
                  let c_app1 =
                    let uu____1067 = mk_lid "app"  in
                    register env2 uu____1067 c_app  in
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
                    let ret =
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
                        binders_of_list
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
                    FStar_Syntax_Util.abs uu____1126 uu____1185 ret  in
                  let c_lift11 =
                    let uu____1239 = mk_lid "lift1"  in
                    register env2 uu____1239 c_lift1  in
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
                    let ret =
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
                        binders_of_list
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
                    FStar_Syntax_Util.abs uu____1327 uu____1400 ret  in
                  let c_lift21 =
                    let uu____1481 = mk_lid "lift2"  in
                    register env2 uu____1481 c_lift2  in
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
                    let ret =
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
                          let uu____1630 = args_of_binders gamma  in
                          uu____1628 :: uu____1630  in
                        FStar_Syntax_Util.mk_app uu____1614 uu____1617  in
                      FStar_Syntax_Util.abs uu____1576 uu____1611 ret  in
                    let uu____1633 =
                      let uu____1634 = mk_all_implicit binders  in
                      let uu____1641 =
                        binders_of_list
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1634 uu____1641  in
                    FStar_Syntax_Util.abs uu____1633 body ret  in
                  let c_push1 =
                    let uu____1686 = mk_lid "push"  in
                    register env2 uu____1686 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > Prims.int_zero
                    then
                      let uu____1713 =
                        let uu____1714 =
                          let uu____1731 = args_of_binders binders  in
                          (c, uu____1731)  in
                        FStar_Syntax_Syntax.Tm_app uu____1714  in
                      mk uu____1713
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
                    register env2 uu____1919 wp_if_then_else  in
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
                    register env2 uu____2055 wp_close  in
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
                  let mk_forall x body =
                    let uu____2080 =
                      let uu____2081 =
                        let uu____2098 =
                          let uu____2109 =
                            let uu____2118 =
                              let uu____2119 =
                                let uu____2120 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____2120]  in
                              FStar_Syntax_Util.abs uu____2119 body
                                ret_tot_type
                               in
                            FStar_Syntax_Syntax.as_arg uu____2118  in
                          [uu____2109]  in
                        (FStar_Syntax_Util.tforall, uu____2098)  in
                      FStar_Syntax_Syntax.Tm_app uu____2081  in
                    FStar_Syntax_Syntax.mk uu____2080 FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2178 =
                      let uu____2179 = FStar_Syntax_Subst.compress t  in
                      uu____2179.FStar_Syntax_Syntax.n  in
                    match uu____2178 with
                    | FStar_Syntax_Syntax.Tm_type uu____2183 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2216  ->
                              match uu____2216 with
                              | (b,uu____2225) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2230 -> true  in
                  let rec is_monotonic t =
                    let uu____2243 =
                      let uu____2244 = FStar_Syntax_Subst.compress t  in
                      uu____2244.FStar_Syntax_Syntax.n  in
                    match uu____2243 with
                    | FStar_Syntax_Syntax.Tm_type uu____2248 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2281  ->
                              match uu____2281 with
                              | (b,uu____2290) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2295 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env2 t
                       in
                    let uu____2369 =
                      let uu____2370 = FStar_Syntax_Subst.compress t1  in
                      uu____2370.FStar_Syntax_Syntax.n  in
                    match uu____2369 with
                    | FStar_Syntax_Syntax.Tm_type uu____2375 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2378);
                                      FStar_Syntax_Syntax.pos = uu____2379;
                                      FStar_Syntax_Syntax.vars = uu____2380;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2424 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2424
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2434 =
                              let uu____2437 =
                                let uu____2448 =
                                  let uu____2457 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2457  in
                                [uu____2448]  in
                              FStar_Syntax_Util.mk_app x uu____2437  in
                            let uu____2474 =
                              let uu____2477 =
                                let uu____2488 =
                                  let uu____2497 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2497  in
                                [uu____2488]  in
                              FStar_Syntax_Util.mk_app y uu____2477  in
                            mk_rel1 b uu____2434 uu____2474  in
                          mk_forall a11 body
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
                             let uu____2521 =
                               let uu____2524 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2527 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2524 uu____2527  in
                             let uu____2530 =
                               let uu____2533 =
                                 let uu____2536 =
                                   let uu____2547 =
                                     let uu____2556 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2556
                                      in
                                   [uu____2547]  in
                                 FStar_Syntax_Util.mk_app x uu____2536  in
                               let uu____2573 =
                                 let uu____2576 =
                                   let uu____2587 =
                                     let uu____2596 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2596
                                      in
                                   [uu____2587]  in
                                 FStar_Syntax_Util.mk_app y uu____2576  in
                               mk_rel1 b uu____2533 uu____2573  in
                             FStar_Syntax_Util.mk_imp uu____2521 uu____2530
                              in
                           let uu____2613 = mk_forall a21 body  in
                           mk_forall a11 uu____2613)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2616);
                                      FStar_Syntax_Syntax.pos = uu____2617;
                                      FStar_Syntax_Syntax.vars = uu____2618;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2662 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2662
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2672 =
                              let uu____2675 =
                                let uu____2686 =
                                  let uu____2695 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2695  in
                                [uu____2686]  in
                              FStar_Syntax_Util.mk_app x uu____2675  in
                            let uu____2712 =
                              let uu____2715 =
                                let uu____2726 =
                                  let uu____2735 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2735  in
                                [uu____2726]  in
                              FStar_Syntax_Util.mk_app y uu____2715  in
                            mk_rel1 b uu____2672 uu____2712  in
                          mk_forall a11 body
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
                             let uu____2759 =
                               let uu____2762 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2765 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2762 uu____2765  in
                             let uu____2768 =
                               let uu____2771 =
                                 let uu____2774 =
                                   let uu____2785 =
                                     let uu____2794 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2794
                                      in
                                   [uu____2785]  in
                                 FStar_Syntax_Util.mk_app x uu____2774  in
                               let uu____2811 =
                                 let uu____2814 =
                                   let uu____2825 =
                                     let uu____2834 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2834
                                      in
                                   [uu____2825]  in
                                 FStar_Syntax_Util.mk_app y uu____2814  in
                               mk_rel1 b uu____2771 uu____2811  in
                             FStar_Syntax_Util.mk_imp uu____2759 uu____2768
                              in
                           let uu____2851 = mk_forall a21 body  in
                           mk_forall a11 uu____2851)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___229_2890 = t1  in
                          let uu____2891 =
                            let uu____2892 =
                              let uu____2907 =
                                let uu____2910 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2910  in
                              ([binder], uu____2907)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2892  in
                          {
                            FStar_Syntax_Syntax.n = uu____2891;
                            FStar_Syntax_Syntax.pos =
                              (uu___229_2890.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___229_2890.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow ([],uu____2933) ->
                        failwith "impossible: arrow with empty binders"
                    | uu____2955 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                            FStar_Syntax_Syntax.delta_constant] env2 t
                         in
                      let uu____2992 =
                        let uu____2993 = FStar_Syntax_Subst.compress t1  in
                        uu____2993.FStar_Syntax_Syntax.n  in
                      match uu____2992 with
                      | FStar_Syntax_Syntax.Tm_type uu____2996 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head,args) when
                          let uu____3023 = FStar_Syntax_Subst.compress head
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3023
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3044 =
                                let uu____3045 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env2
                                  uu____3045 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3044
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   Prims.int_one)
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3075 =
                            let uu____3086 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3104  ->
                                     match uu____3104 with
                                     | (t2,q) ->
                                         let uu____3124 = project i x  in
                                         let uu____3127 = project i y  in
                                         mk_stronger t2 uu____3124 uu____3127)
                                args
                               in
                            match uu____3086 with
                            | [] ->
                                failwith
                                  "Impossible: empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3075 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3181);
                                      FStar_Syntax_Syntax.pos = uu____3182;
                                      FStar_Syntax_Syntax.vars = uu____3183;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3227  ->
                                   match uu____3227 with
                                   | (bv,q) ->
                                       let uu____3241 =
                                         let uu____3243 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3243  in
                                       FStar_Syntax_Syntax.gen_bv uu____3241
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3252 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3252) bvs
                             in
                          let body =
                            let uu____3254 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3257 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3254 uu____3257  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall bv body1) bvs
                            body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3266);
                                      FStar_Syntax_Syntax.pos = uu____3267;
                                      FStar_Syntax_Syntax.vars = uu____3268;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3312  ->
                                   match uu____3312 with
                                   | (bv,q) ->
                                       let uu____3326 =
                                         let uu____3328 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3328  in
                                       FStar_Syntax_Syntax.gen_bv uu____3326
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3337 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3337) bvs
                             in
                          let body =
                            let uu____3339 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3342 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3339 uu____3342  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall bv body1) bvs
                            body
                      | uu____3349 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3352 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3355 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3358 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3352 uu____3355 uu____3358  in
                    let uu____3361 =
                      let uu____3362 =
                        binders_of_list
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3362  in
                    FStar_Syntax_Util.abs uu____3361 body ret_tot_type  in
                  let stronger1 =
                    let uu____3404 = mk_lid "stronger"  in
                    register env2 uu____3404 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3412 = FStar_Util.prefix gamma  in
                    match uu____3412 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq =
                            let uu____3478 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3478
                             in
                          let uu____3483 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq  in
                          match uu____3483 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3493 = args_of_binders binders1  in
                                FStar_Syntax_Util.mk_app k_tm uu____3493  in
                              let guard_free =
                                let uu____3505 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3505  in
                              let pat =
                                let uu____3509 =
                                  let uu____3520 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3520]  in
                                FStar_Syntax_Util.mk_app guard_free
                                  uu____3509
                                 in
                              let pattern_guarded_body =
                                let uu____3548 =
                                  let uu____3549 =
                                    let uu____3556 =
                                      let uu____3557 =
                                        let uu____3578 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1
                                           in
                                        let uu____3583 =
                                          let uu____3596 =
                                            let uu____3607 =
                                              FStar_Syntax_Syntax.as_arg pat
                                               in
                                            [uu____3607]  in
                                          [uu____3596]  in
                                        (uu____3578, uu____3583)  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3557
                                       in
                                    (body, uu____3556)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3549  in
                                mk uu____3548  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3670 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3679 =
                            let uu____3682 =
                              let uu____3683 =
                                let uu____3686 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3689 =
                                  let uu____3700 = args_of_binders wp_args
                                     in
                                  let uu____3703 =
                                    let uu____3706 =
                                      let uu____3707 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3707
                                       in
                                    [uu____3706]  in
                                  FStar_List.append uu____3700 uu____3703  in
                                FStar_Syntax_Util.mk_app uu____3686
                                  uu____3689
                                 in
                              FStar_Syntax_Util.mk_imp equiv uu____3683  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3682
                             in
                          FStar_Syntax_Util.abs gamma uu____3679
                            ret_gtot_type
                           in
                        let uu____3708 =
                          let uu____3709 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3709  in
                        FStar_Syntax_Util.abs uu____3708 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3725 = mk_lid "ite_wp"  in
                    register env2 uu____3725 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3733 = FStar_Util.prefix gamma  in
                    match uu____3733 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3791 =
                            let uu____3792 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3799 =
                              let uu____3810 =
                                let uu____3819 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3819  in
                              [uu____3810]  in
                            FStar_Syntax_Util.mk_app uu____3792 uu____3799
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3791
                           in
                        let uu____3836 =
                          let uu____3837 =
                            let uu____3846 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3846 gamma  in
                          FStar_List.append binders uu____3837  in
                        FStar_Syntax_Util.abs uu____3836 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3868 = mk_lid "null_wp"  in
                    register env2 uu____3868 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3881 =
                        let uu____3892 =
                          let uu____3895 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3896 =
                            let uu____3899 =
                              let uu____3900 =
                                let uu____3911 =
                                  let uu____3920 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3920  in
                                [uu____3911]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3900
                               in
                            let uu____3937 =
                              let uu____3940 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3940]  in
                            uu____3899 :: uu____3937  in
                          uu____3895 :: uu____3896  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3892
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3881  in
                    let uu____3949 =
                      let uu____3950 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3950  in
                    FStar_Syntax_Util.abs uu____3949 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3966 = mk_lid "wp_trivial"  in
                    register env2 uu____3966 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3972 =
                      FStar_TypeChecker_Env.debug env2
                        (FStar_Options.Other "ED")
                       in
                    if uu____3972
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let ed_combs =
                      match ed.FStar_Syntax_Syntax.combinators with
                      | FStar_Syntax_Syntax.DM4F_eff combs ->
                          let uu____3986 =
                            let uu___340_3987 = combs  in
                            let uu____3988 =
                              let uu____3989 = c stronger2  in
                              ([], uu____3989)  in
                            let uu____3996 =
                              let uu____3997 = c wp_if_then_else2  in
                              ([], uu____3997)  in
                            let uu____4004 =
                              let uu____4005 = c ite_wp2  in ([], uu____4005)
                               in
                            let uu____4012 =
                              let uu____4013 = c wp_close2  in
                              ([], uu____4013)  in
                            let uu____4020 =
                              let uu____4021 = c wp_trivial2  in
                              ([], uu____4021)  in
                            {
                              FStar_Syntax_Syntax.ret_wp =
                                (uu___340_3987.FStar_Syntax_Syntax.ret_wp);
                              FStar_Syntax_Syntax.bind_wp =
                                (uu___340_3987.FStar_Syntax_Syntax.bind_wp);
                              FStar_Syntax_Syntax.stronger = uu____3988;
                              FStar_Syntax_Syntax.if_then_else = uu____3996;
                              FStar_Syntax_Syntax.ite_wp = uu____4004;
                              FStar_Syntax_Syntax.close_wp = uu____4012;
                              FStar_Syntax_Syntax.trivial = uu____4020;
                              FStar_Syntax_Syntax.repr =
                                (uu___340_3987.FStar_Syntax_Syntax.repr);
                              FStar_Syntax_Syntax.return_repr =
                                (uu___340_3987.FStar_Syntax_Syntax.return_repr);
                              FStar_Syntax_Syntax.bind_repr =
                                (uu___340_3987.FStar_Syntax_Syntax.bind_repr)
                            }  in
                          FStar_Syntax_Syntax.DM4F_eff uu____3986
                      | uu____4028 ->
                          failwith
                            "Impossible! For a DM4F effect combinators must be in DM4f_eff"
                       in
                    let uu____4030 =
                      let uu____4031 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4031  in
                    (uu____4030,
                      (let uu___344_4058 = ed  in
                       {
                         FStar_Syntax_Syntax.mname =
                           (uu___344_4058.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___344_4058.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.univs =
                           (uu___344_4058.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___344_4058.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature =
                           (uu___344_4058.FStar_Syntax_Syntax.signature);
                         FStar_Syntax_Syntax.combinators = ed_combs;
                         FStar_Syntax_Syntax.actions =
                           (uu___344_4058.FStar_Syntax_Syntax.actions);
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___344_4058.FStar_Syntax_Syntax.eff_attrs)
                       }))))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env1  -> env1.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___349_4076 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___349_4076.subst);
        tc_const = (uu___349_4076.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4097 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4116 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4136) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_4150  ->
                match uu___0_4150 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4153 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4155 ->
        let uu____4156 =
          let uu____4162 =
            let uu____4164 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4164
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4162)  in
        FStar_Errors.raise_error uu____4156 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_4174  ->
    match uu___1_4174 with
    | N t ->
        let uu____4177 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4177
    | M t ->
        let uu____4181 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4181
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n  ->
    match n with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4190,c) -> nm_of_comp c
    | uu____4212 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4225 = nm_of_comp c  in
    match uu____4225 with | M uu____4227 -> true | N uu____4229 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4240 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4256 =
        let uu____4265 =
          let uu____4272 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4272  in
        [uu____4265]  in
      let uu____4291 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4256 uu____4291  in
    let uu____4294 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4294
  
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk  ->
    fun env1  ->
      fun a  ->
        let uu____4336 =
          let uu____4337 =
            let uu____4352 =
              let uu____4361 =
                let uu____4368 =
                  let uu____4369 = star_type' env1 a  in
                  FStar_Syntax_Syntax.null_bv uu____4369  in
                let uu____4370 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4368, uu____4370)  in
              [uu____4361]  in
            let uu____4388 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4352, uu____4388)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4337  in
        mk uu____4336

and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun t  ->
      let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos  in
      let mk_star_to_type1 = mk_star_to_type mk  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4428) ->
          let binders1 =
            FStar_List.map
              (fun uu____4474  ->
                 match uu____4474 with
                 | (bv,aqual) ->
                     let uu____4493 =
                       let uu___399_4494 = bv  in
                       let uu____4495 =
                         star_type' env1 bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___399_4494.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___399_4494.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4495
                       }  in
                     (uu____4493, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4500,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4502);
                             FStar_Syntax_Syntax.pos = uu____4503;
                             FStar_Syntax_Syntax.vars = uu____4504;_})
               ->
               let uu____4533 =
                 let uu____4534 =
                   let uu____4549 =
                     let uu____4552 = star_type' env1 hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4552  in
                   (binders1, uu____4549)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4534  in
               mk uu____4533
           | uu____4563 ->
               let uu____4564 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4564 with
                | N hn ->
                    let uu____4566 =
                      let uu____4567 =
                        let uu____4582 =
                          let uu____4585 = star_type' env1 hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4585  in
                        (binders1, uu____4582)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4567  in
                    mk uu____4566
                | M a ->
                    let uu____4597 =
                      let uu____4598 =
                        let uu____4613 =
                          let uu____4622 =
                            let uu____4631 =
                              let uu____4638 =
                                let uu____4639 = mk_star_to_type1 env1 a  in
                                FStar_Syntax_Syntax.null_bv uu____4639  in
                              let uu____4640 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4638, uu____4640)  in
                            [uu____4631]  in
                          FStar_List.append binders1 uu____4622  in
                        let uu____4664 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4613, uu____4664)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4598  in
                    mk uu____4597))
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let debug t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4758 = f x  in
                    FStar_Util.string_builder_append strb uu____4758);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4767 = f x1  in
                         FStar_Util.string_builder_append strb uu____4767))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4771 =
              let uu____4777 =
                let uu____4779 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4781 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4779 uu____4781
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4777)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4771  in
          let rec is_non_dependent_arrow ty n =
            let uu____4803 =
              let uu____4804 = FStar_Syntax_Subst.compress ty  in
              uu____4804.FStar_Syntax_Syntax.n  in
            match uu____4803 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4830 =
                  let uu____4832 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4832  in
                if uu____4830
                then false
                else
                  (try
                     (fun uu___448_4849  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4873 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4873 s  in
                              let uu____4876 =
                                let uu____4878 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4878  in
                              if uu____4876
                              then
                                (debug ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4884 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4884 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4909  ->
                                          match uu____4909 with
                                          | (bv,uu____4921) ->
                                              (non_dependent_or_raise s
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s))
                                     FStar_Syntax_Syntax.no_names binders1
                                    in
                                 let ct = FStar_Syntax_Util.comp_result c1
                                    in
                                 (non_dependent_or_raise s ct;
                                  (let k = n - (FStar_List.length binders1)
                                      in
                                   if k > Prims.int_zero
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found  -> false)
            | uu____4949 ->
                ((let uu____4951 =
                    let uu____4957 =
                      let uu____4959 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4959
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4957)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4951);
                 false)
             in
          let rec is_valid_application head1 =
            let uu____4975 =
              let uu____4976 = FStar_Syntax_Subst.compress head1  in
              uu____4976.FStar_Syntax_Syntax.n  in
            match uu____4975 with
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
                  (let uu____4982 = FStar_Syntax_Subst.compress head1  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4982)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4985 =
                  FStar_TypeChecker_Env.lookup_lid env1.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4985 with
                 | ((uu____4995,ty),uu____4997) ->
                     let uu____5002 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5002
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env1.tcenv
                           t1
                          in
                       let uu____5015 =
                         let uu____5016 = FStar_Syntax_Subst.compress res  in
                         uu____5016.FStar_Syntax_Syntax.n  in
                       (match uu____5015 with
                        | FStar_Syntax_Syntax.Tm_app uu____5020 -> true
                        | uu____5038 ->
                            ((let uu____5040 =
                                let uu____5046 =
                                  let uu____5048 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5048
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5046)
                                 in
                              FStar_Errors.log_issue
                                head1.FStar_Syntax_Syntax.pos uu____5040);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5056 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5058 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5061) ->
                is_valid_application t2
            | uu____5066 -> false  in
          let uu____5068 = is_valid_application head  in
          if uu____5068
          then
            let uu____5071 =
              let uu____5072 =
                let uu____5089 =
                  FStar_List.map
                    (fun uu____5118  ->
                       match uu____5118 with
                       | (t2,qual) ->
                           let uu____5143 = star_type' env1 t2  in
                           (uu____5143, qual)) args
                   in
                (head, uu____5089)  in
              FStar_Syntax_Syntax.Tm_app uu____5072  in
            mk uu____5071
          else
            (let uu____5160 =
               let uu____5166 =
                 let uu____5168 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5168
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5166)  in
             FStar_Errors.raise_err uu____5160)
      | FStar_Syntax_Syntax.Tm_bvar uu____5172 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5173 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5174 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5175 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5203 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5203 with
           | (binders1,repr1) ->
               let env2 =
                 let uu___520_5211 = env1  in
                 let uu____5212 =
                   FStar_TypeChecker_Env.push_binders env1.tcenv binders1  in
                 {
                   tcenv = uu____5212;
                   subst = (uu___520_5211.subst);
                   tc_const = (uu___520_5211.tc_const)
                 }  in
               let repr2 = star_type' env2 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env1 x1.FStar_Syntax_Syntax.sort  in
          let subst = [FStar_Syntax_Syntax.DB (Prims.int_zero, x1)]  in
          let t3 = FStar_Syntax_Subst.subst subst t2  in
          let t4 = star_type' env1 t3  in
          let subst1 = [FStar_Syntax_Syntax.NM (x1, Prims.int_zero)]  in
          let t5 = FStar_Syntax_Subst.subst subst1 t4  in
          mk
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___535_5239 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___535_5239.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___535_5239.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5246 =
            let uu____5247 =
              let uu____5254 = star_type' env1 t2  in (uu____5254, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5247  in
          mk uu____5246
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5306 =
            let uu____5307 =
              let uu____5334 = star_type' env1 e  in
              let uu____5337 =
                let uu____5354 =
                  let uu____5363 = star_type' env1 t2  in
                  FStar_Util.Inl uu____5363  in
                (uu____5354, FStar_Pervasives_Native.None)  in
              (uu____5334, uu____5337, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5307  in
          mk uu____5306
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5451 =
            let uu____5452 =
              let uu____5479 = star_type' env1 e  in
              let uu____5482 =
                let uu____5499 =
                  let uu____5508 =
                    star_type' env1 (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5508  in
                (uu____5499, FStar_Pervasives_Native.None)  in
              (uu____5479, uu____5482, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5452  in
          mk uu____5451
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5549,(uu____5550,FStar_Pervasives_Native.Some uu____5551),uu____5552)
          ->
          let uu____5601 =
            let uu____5607 =
              let uu____5609 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5609
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5607)  in
          FStar_Errors.raise_err uu____5601
      | FStar_Syntax_Syntax.Tm_refine uu____5613 ->
          let uu____5620 =
            let uu____5626 =
              let uu____5628 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5628
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5626)  in
          FStar_Errors.raise_err uu____5620
      | FStar_Syntax_Syntax.Tm_uinst uu____5632 ->
          let uu____5639 =
            let uu____5645 =
              let uu____5647 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5647
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5645)  in
          FStar_Errors.raise_err uu____5639
      | FStar_Syntax_Syntax.Tm_quoted uu____5651 ->
          let uu____5658 =
            let uu____5664 =
              let uu____5666 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5666
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5664)  in
          FStar_Errors.raise_err uu____5658
      | FStar_Syntax_Syntax.Tm_constant uu____5670 ->
          let uu____5671 =
            let uu____5677 =
              let uu____5679 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5679
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5677)  in
          FStar_Errors.raise_err uu____5671
      | FStar_Syntax_Syntax.Tm_match uu____5683 ->
          let uu____5706 =
            let uu____5712 =
              let uu____5714 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5714
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5712)  in
          FStar_Errors.raise_err uu____5706
      | FStar_Syntax_Syntax.Tm_let uu____5718 ->
          let uu____5732 =
            let uu____5738 =
              let uu____5740 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5740
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5738)  in
          FStar_Errors.raise_err uu____5732
      | FStar_Syntax_Syntax.Tm_uvar uu____5744 ->
          let uu____5757 =
            let uu____5763 =
              let uu____5765 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5765
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5763)  in
          FStar_Errors.raise_err uu____5757
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5769 =
            let uu____5775 =
              let uu____5777 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5777
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5775)  in
          FStar_Errors.raise_err uu____5769
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5782 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env1 uu____5782
      | FStar_Syntax_Syntax.Tm_delayed uu____5785 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_5809  ->
    match uu___3_5809 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_5820  ->
                match uu___2_5820 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5823 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5833 =
      let uu____5834 = FStar_Syntax_Subst.compress t  in
      uu____5834.FStar_Syntax_Syntax.n  in
    match uu____5833 with
    | FStar_Syntax_Syntax.Tm_app (head,args) when
        FStar_Syntax_Util.is_tuple_constructor head ->
        let r =
          let uu____5866 =
            let uu____5867 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5867  in
          is_C uu____5866  in
        if r
        then
          ((let uu____5891 =
              let uu____5893 =
                FStar_List.for_all
                  (fun uu____5904  ->
                     match uu____5904 with | (h,uu____5913) -> is_C h) args
                 in
              Prims.op_Negation uu____5893  in
            if uu____5891
            then
              let uu____5919 =
                let uu____5925 =
                  let uu____5927 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not a C-type (A * C): %s" uu____5927
                   in
                (FStar_Errors.Error_UnexpectedDM4FType, uu____5925)  in
              FStar_Errors.raise_error uu____5919 t.FStar_Syntax_Syntax.pos
            else ());
           true)
        else
          ((let uu____5937 =
              let uu____5939 =
                FStar_List.for_all
                  (fun uu____5951  ->
                     match uu____5951 with
                     | (h,uu____5960) ->
                         let uu____5965 = is_C h  in
                         Prims.op_Negation uu____5965) args
                 in
              Prims.op_Negation uu____5939  in
            if uu____5937
            then
              let uu____5968 =
                let uu____5974 =
                  let uu____5976 = FStar_Syntax_Print.term_to_string t  in
                  FStar_Util.format1 "Not a C-type (C * A): %s" uu____5976
                   in
                (FStar_Errors.Error_UnexpectedDM4FType, uu____5974)  in
              FStar_Errors.raise_error uu____5968 t.FStar_Syntax_Syntax.pos
            else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6005 = nm_of_comp comp  in
        (match uu____6005 with
         | M t1 ->
             ((let uu____6009 = is_C t1  in
               if uu____6009
               then
                 let uu____6012 =
                   let uu____6018 =
                     let uu____6020 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.format1 "Not a C-type (C -> C): %s"
                       uu____6020
                      in
                   (FStar_Errors.Error_UnexpectedDM4FType, uu____6018)  in
                 FStar_Errors.raise_error uu____6012
                   t1.FStar_Syntax_Syntax.pos
               else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6029) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6035) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6041,uu____6042) -> is_C t1
    | uu____6083 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env1  ->
    fun t  ->
      fun e  ->
        let mk x = FStar_Syntax_Syntax.mk x e.FStar_Syntax_Syntax.pos  in
        let p_type = mk_star_to_type mk env1 t  in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type
           in
        let body =
          let uu____6119 =
            let uu____6120 =
              let uu____6137 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6140 =
                let uu____6151 =
                  let uu____6160 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6160)  in
                [uu____6151]  in
              (uu____6137, uu____6140)  in
            FStar_Syntax_Syntax.Tm_app uu____6120  in
          mk uu____6119  in
        let uu____6196 =
          let uu____6197 = FStar_Syntax_Syntax.mk_binder p  in [uu____6197]
           in
        FStar_Syntax_Util.abs uu____6196 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_6222  ->
    match uu___4_6222 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6225 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env1  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6463 =
          match uu____6463 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6500 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6503 =
                       let uu____6505 =
                         FStar_TypeChecker_Rel.teq env1.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6505  in
                     Prims.op_Negation uu____6503)
                   in
                if uu____6500
                then
                  let uu____6507 =
                    let uu____6513 =
                      let uu____6515 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6517 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6519 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6515 uu____6517 uu____6519
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6513)  in
                  FStar_Errors.raise_err uu____6507
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6544 = mk_return env1 t1 s_e  in
                     ((M t1), uu____6544, u_e)))
               | (M t1,N t2) ->
                   let uu____6551 =
                     let uu____6557 =
                       let uu____6559 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6561 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6563 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6559 uu____6561 uu____6563
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6557)
                      in
                   FStar_Errors.raise_err uu____6551)
           in
        let ensure_m env2 e2 =
          let strip_m uu___5_6615 =
            match uu___5_6615 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6631 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6652 =
                let uu____6658 =
                  let uu____6660 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6660
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6658)  in
              FStar_Errors.raise_error uu____6652 e2.FStar_Syntax_Syntax.pos
          | M uu____6670 ->
              let uu____6671 = check env2 e2 context_nm  in
              strip_m uu____6671
           in
        let uu____6678 =
          let uu____6679 = FStar_Syntax_Subst.compress e  in
          uu____6679.FStar_Syntax_Syntax.n  in
        match uu____6678 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6688 ->
            let uu____6689 = infer env1 e  in return_if uu____6689
        | FStar_Syntax_Syntax.Tm_name uu____6696 ->
            let uu____6697 = infer env1 e  in return_if uu____6697
        | FStar_Syntax_Syntax.Tm_fvar uu____6704 ->
            let uu____6705 = infer env1 e  in return_if uu____6705
        | FStar_Syntax_Syntax.Tm_abs uu____6712 ->
            let uu____6731 = infer env1 e  in return_if uu____6731
        | FStar_Syntax_Syntax.Tm_constant uu____6738 ->
            let uu____6739 = infer env1 e  in return_if uu____6739
        | FStar_Syntax_Syntax.Tm_quoted uu____6746 ->
            let uu____6753 = infer env1 e  in return_if uu____6753
        | FStar_Syntax_Syntax.Tm_app uu____6760 ->
            let uu____6777 = infer env1 e  in return_if uu____6777
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6785 = FStar_Syntax_Util.unfold_lazy i  in
            check env1 uu____6785 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env1 binding e2
              (fun env2  -> fun e21  -> check env2 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env1 e0 branches
              (fun env2  -> fun body  -> check env2 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6850) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6856) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6862,uu____6863) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6904 ->
            let uu____6918 =
              let uu____6920 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6920  in
            failwith uu____6918
        | FStar_Syntax_Syntax.Tm_type uu____6929 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6937 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6959 ->
            let uu____6966 =
              let uu____6968 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6968  in
            failwith uu____6966
        | FStar_Syntax_Syntax.Tm_uvar uu____6977 ->
            let uu____6990 =
              let uu____6992 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6992  in
            failwith uu____6990
        | FStar_Syntax_Syntax.Tm_delayed uu____7001 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7023 =
              let uu____7025 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7025  in
            failwith uu____7023

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env1  ->
    fun e  ->
      let mk x = FStar_Syntax_Syntax.mk x e.FStar_Syntax_Syntax.pos  in
      let normalize =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env1.tcenv
         in
      let uu____7055 =
        let uu____7056 = FStar_Syntax_Subst.compress e  in
        uu____7056.FStar_Syntax_Syntax.n  in
      match uu____7055 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7075 = FStar_Syntax_Util.unfold_lazy i  in
          infer env1 uu____7075
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7126;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7127;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7133 =
                  let uu___770_7134 = rc  in
                  let uu____7135 =
                    let uu____7140 =
                      let uu____7143 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst uu____7143  in
                    FStar_Pervasives_Native.Some uu____7140  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___770_7134.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7135;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___770_7134.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7133
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst body  in
          let rc_opt1 = subst_rc_opt subst rc_opt  in
          let env2 =
            let uu___776_7155 = env1  in
            let uu____7156 =
              FStar_TypeChecker_Env.push_binders env1.tcenv binders1  in
            {
              tcenv = uu____7156;
              subst = (uu___776_7155.subst);
              tc_const = (uu___776_7155.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7182  ->
                 match uu____7182 with
                 | (bv,qual) ->
                     let sort = star_type' env2 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___783_7205 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___783_7205.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___783_7205.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7206 =
            FStar_List.fold_left
              (fun uu____7237  ->
                 fun uu____7238  ->
                   match (uu____7237, uu____7238) with
                   | ((env3,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7296 = is_C c  in
                       if uu____7296
                       then
                         let xw =
                           let uu____7306 =
                             let uu____7308 =
                               FStar_Ident.string_of_id
                                 bv.FStar_Syntax_Syntax.ppname
                                in
                             Prims.op_Hat uu____7308 "__w"  in
                           let uu____7311 = star_type' env3 c  in
                           FStar_Syntax_Syntax.gen_bv uu____7306
                             FStar_Pervasives_Native.None uu____7311
                            in
                         let x =
                           let uu___795_7313 = bv  in
                           let uu____7314 =
                             let uu____7317 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env3 c uu____7317  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___795_7313.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___795_7313.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7314
                           }  in
                         let env4 =
                           let uu___798_7319 = env3  in
                           let uu____7320 =
                             let uu____7323 =
                               let uu____7324 =
                                 let uu____7331 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7331)  in
                               FStar_Syntax_Syntax.NT uu____7324  in
                             uu____7323 :: (env3.subst)  in
                           {
                             tcenv = (uu___798_7319.tcenv);
                             subst = uu____7320;
                             tc_const = (uu___798_7319.tc_const)
                           }  in
                         let uu____7336 =
                           let uu____7339 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7340 =
                             let uu____7343 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7343 :: acc  in
                           uu____7339 :: uu____7340  in
                         (env4, uu____7336)
                       else
                         (let x =
                            let uu___801_7349 = bv  in
                            let uu____7350 =
                              star_type' env3 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___801_7349.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___801_7349.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7350
                            }  in
                          let uu____7353 =
                            let uu____7356 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7356 :: acc  in
                          (env3, uu____7353))) (env2, []) binders1
             in
          (match uu____7206 with
           | (env3,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7376 =
                 let check_what =
                   let uu____7402 = is_monadic rc_opt1  in
                   if uu____7402 then check_m else check_n  in
                 let uu____7419 = check_what env3 body1  in
                 match uu____7419 with
                 | (t,s_body,u_body) ->
                     let uu____7439 =
                       let uu____7442 =
                         let uu____7443 = is_monadic rc_opt1  in
                         if uu____7443 then M t else N t  in
                       comp_of_nm uu____7442  in
                     (uu____7439, s_body, u_body)
                  in
               (match uu____7376 with
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
                                 let uu____7483 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_7489  ->
                                           match uu___6_7489 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7492 -> false))
                                    in
                                 if uu____7483
                                 then
                                   let uu____7495 =
                                     FStar_List.filter
                                       (fun uu___7_7499  ->
                                          match uu___7_7499 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7502 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7495
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7513 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_7519  ->
                                         match uu___8_7519 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7522 -> false))
                                  in
                               if uu____7513
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_7531  ->
                                        match uu___9_7531 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7534 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7536 =
                                   let uu____7537 =
                                     let uu____7542 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7542
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7537 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7536
                               else
                                 (let uu____7549 =
                                    let uu___842_7550 = rc  in
                                    let uu____7551 =
                                      let uu____7556 = star_type' env3 rt  in
                                      FStar_Pervasives_Native.Some uu____7556
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___842_7550.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7551;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___842_7550.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7549))
                       in
                    let uu____7561 =
                      let comp1 =
                        let uu____7569 = is_monadic rc_opt1  in
                        let uu____7571 =
                          FStar_Syntax_Subst.subst env3.subst s_body  in
                        trans_G env3 (FStar_Syntax_Util.comp_result comp)
                          uu____7569 uu____7571
                         in
                      let uu____7572 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7572,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7561 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7610 =
                             let uu____7611 =
                               let uu____7630 =
                                 let uu____7633 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7633 s_rc_opt  in
                               (s_binders1, s_body1, uu____7630)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7611  in
                           mk uu____7610  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7653 =
                             let uu____7654 =
                               let uu____7673 =
                                 let uu____7676 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7676 u_rc_opt  in
                               (u_binders2, u_body2, uu____7673)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7654  in
                           mk uu____7653  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7692;_};
            FStar_Syntax_Syntax.fv_delta = uu____7693;
            FStar_Syntax_Syntax.fv_qual = uu____7694;_}
          ->
          let uu____7697 =
            let uu____7702 = FStar_TypeChecker_Env.lookup_lid env1.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7702  in
          (match uu____7697 with
           | (uu____7733,t) ->
               let uu____7735 = let uu____7736 = normalize t  in N uu____7736
                  in
               (uu____7735, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7737;
             FStar_Syntax_Syntax.vars = uu____7738;_},a::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____7817 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7817 with
           | (unary_op,uu____7841) ->
               let head = mk (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))  in
               let t = mk (FStar_Syntax_Syntax.Tm_app (head, rest1))  in
               infer env1 t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7912;
             FStar_Syntax_Syntax.vars = uu____7913;_},a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest  in
          let uu____8009 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8009 with
           | (unary_op,uu____8033) ->
               let head =
                 mk (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk (FStar_Syntax_Syntax.Tm_app (head, rest1))  in
               infer env1 t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8112;
             FStar_Syntax_Syntax.vars = uu____8113;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8151 = infer env1 a  in
          (match uu____8151 with
           | (t,s,u) ->
               let uu____8167 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8167 with
                | (head,uu____8191) ->
                    let uu____8216 =
                      let uu____8217 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8217  in
                    let uu____8218 =
                      let uu____8219 =
                        let uu____8220 =
                          let uu____8237 =
                            let uu____8248 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8248]  in
                          (head, uu____8237)  in
                        FStar_Syntax_Syntax.Tm_app uu____8220  in
                      mk uu____8219  in
                    let uu____8285 =
                      let uu____8286 =
                        let uu____8287 =
                          let uu____8304 =
                            let uu____8315 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8315]  in
                          (head, uu____8304)  in
                        FStar_Syntax_Syntax.Tm_app uu____8287  in
                      mk uu____8286  in
                    (uu____8216, uu____8218, uu____8285)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8352;
             FStar_Syntax_Syntax.vars = uu____8353;_},(a1,uu____8355)::a2::[])
          ->
          let uu____8411 = infer env1 a1  in
          (match uu____8411 with
           | (t,s,u) ->
               let uu____8427 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8427 with
                | (head,uu____8451) ->
                    let uu____8476 =
                      let uu____8477 =
                        let uu____8478 =
                          let uu____8495 =
                            let uu____8506 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8506; a2]  in
                          (head, uu____8495)  in
                        FStar_Syntax_Syntax.Tm_app uu____8478  in
                      mk uu____8477  in
                    let uu____8551 =
                      let uu____8552 =
                        let uu____8553 =
                          let uu____8570 =
                            let uu____8581 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8581; a2]  in
                          (head, uu____8570)  in
                        FStar_Syntax_Syntax.Tm_app uu____8553  in
                      mk uu____8552  in
                    (t, uu____8476, uu____8551)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8626;
             FStar_Syntax_Syntax.vars = uu____8627;_},uu____8628)
          ->
          let uu____8653 =
            let uu____8659 =
              let uu____8661 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8661
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8659)  in
          FStar_Errors.raise_error uu____8653 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8671;
             FStar_Syntax_Syntax.vars = uu____8672;_},uu____8673)
          ->
          let uu____8698 =
            let uu____8704 =
              let uu____8706 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8706
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8704)  in
          FStar_Errors.raise_error uu____8698 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let uu____8742 = check_n env1 head  in
          (match uu____8742 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8765 =
                   let uu____8766 = FStar_Syntax_Subst.compress t  in
                   uu____8766.FStar_Syntax_Syntax.n  in
                 match uu____8765 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8770 -> true
                 | uu____8786 -> false  in
               let rec flatten t =
                 let uu____8808 =
                   let uu____8809 = FStar_Syntax_Subst.compress t  in
                   uu____8809.FStar_Syntax_Syntax.n  in
                 match uu____8808 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8828);
                                FStar_Syntax_Syntax.pos = uu____8829;
                                FStar_Syntax_Syntax.vars = uu____8830;_})
                     when is_arrow t1 ->
                     let uu____8859 = flatten t1  in
                     (match uu____8859 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8959,uu____8960)
                     -> flatten e1
                 | uu____9001 ->
                     let uu____9002 =
                       let uu____9008 =
                         let uu____9010 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9010
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9008)  in
                     FStar_Errors.raise_err uu____9002
                  in
               let uu____9028 = flatten t_head  in
               (match uu____9028 with
                | (binders,comp) ->
                    let n = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9103 =
                          let uu____9109 =
                            let uu____9111 = FStar_Util.string_of_int n  in
                            let uu____9113 =
                              FStar_Util.string_of_int (n' - n)  in
                            let uu____9115 = FStar_Util.string_of_int n  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9111 uu____9113 uu____9115
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9109)
                           in
                        FStar_Errors.raise_err uu____9103)
                     else ();
                     (let uu____9121 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9121 with
                      | (binders1,comp1) ->
                          let rec final_type subst uu____9174 args1 =
                            match uu____9174 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9274 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         comp2
                                        in
                                     nm_of_comp uu____9274
                                 | (binders3,[]) ->
                                     let uu____9312 =
                                       let uu____9313 =
                                         let uu____9316 =
                                           let uu____9317 =
                                             mk
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst
                                             uu____9317
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9316
                                          in
                                       uu____9313.FStar_Syntax_Syntax.n  in
                                     (match uu____9312 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9350 =
                                            let uu____9351 =
                                              let uu____9352 =
                                                let uu____9367 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9367)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9352
                                               in
                                            mk uu____9351  in
                                          N uu____9350
                                      | uu____9380 -> failwith "wat?")
                                 | ([],uu____9382::uu____9383) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9436)::binders3,(arg,uu____9439)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9526 = FStar_List.splitAt n' binders1  in
                          (match uu____9526 with
                           | (binders2,uu____9560) ->
                               let uu____9593 =
                                 let uu____9616 =
                                   FStar_List.map2
                                     (fun uu____9678  ->
                                        fun uu____9679  ->
                                          match (uu____9678, uu____9679) with
                                          | ((bv,uu____9727),(arg,q)) ->
                                              let uu____9756 =
                                                let uu____9757 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9757.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9756 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9778 ->
                                                   let uu____9779 =
                                                     let uu____9786 =
                                                       star_type' env1 arg
                                                        in
                                                     (uu____9786, q)  in
                                                   (uu____9779, [(arg, q)])
                                               | uu____9823 ->
                                                   let uu____9824 =
                                                     check_n env1 arg  in
                                                   (match uu____9824 with
                                                    | (uu____9849,s_arg,u_arg)
                                                        ->
                                                        let uu____9852 =
                                                          let uu____9861 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9861
                                                          then
                                                            let uu____9872 =
                                                              let uu____9879
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env1.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9879, q)
                                                               in
                                                            [uu____9872;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9852))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9616  in
                               (match uu____9593 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10007 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10020 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10007, uu____10020)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env1 binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env1 e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10089) -> infer env1 e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10095) -> infer env1 e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10101,uu____10102) ->
          infer env1 e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10144 =
            let uu____10145 = env1.tc_const c  in N uu____10145  in
          (uu____10144, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10152 ->
          let uu____10166 =
            let uu____10168 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10168  in
          failwith uu____10166
      | FStar_Syntax_Syntax.Tm_type uu____10177 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10185 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10207 ->
          let uu____10214 =
            let uu____10216 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10216  in
          failwith uu____10214
      | FStar_Syntax_Syntax.Tm_uvar uu____10225 ->
          let uu____10238 =
            let uu____10240 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10240  in
          failwith uu____10238
      | FStar_Syntax_Syntax.Tm_delayed uu____10249 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10271 =
            let uu____10273 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10273  in
          failwith uu____10271

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
  fun env1  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk x = FStar_Syntax_Syntax.mk x e0.FStar_Syntax_Syntax.pos  in
          let uu____10322 = check_n env1 e0  in
          match uu____10322 with
          | (uu____10335,s_e0,u_e0) ->
              let uu____10338 =
                let uu____10367 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10428 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10428 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env2 =
                             let uu___1117_10470 = env1  in
                             let uu____10471 =
                               let uu____10472 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env1.tcenv
                                 uu____10472
                                in
                             {
                               tcenv = uu____10471;
                               subst = (uu___1117_10470.subst);
                               tc_const = (uu___1117_10470.tc_const)
                             }  in
                           let uu____10475 = f env2 body  in
                           (match uu____10475 with
                            | (nm1,s_body,u_body) ->
                                (nm1,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10547 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10367  in
              (match uu____10338 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10653 = FStar_List.hd nms  in
                     match uu____10653 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10662  ->
                          match uu___10_10662 with
                          | M uu____10664 -> true
                          | uu____10666 -> false) nms
                      in
                   let uu____10668 =
                     let uu____10705 =
                       FStar_List.map2
                         (fun nm1  ->
                            fun uu____10795  ->
                              match uu____10795 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm1, has_m) with
                                   | (N t2,false ) ->
                                       (nm1, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm1, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____10979 =
                                         check env1 original_body (M t2)  in
                                       (match uu____10979 with
                                        | (uu____11016,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11055,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10705  in
                   (match uu____10668 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk env1 t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____11244  ->
                                 match uu____11244 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11295 =
                                         let uu____11296 =
                                           let uu____11313 =
                                             let uu____11324 =
                                               let uu____11333 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11336 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11333, uu____11336)  in
                                             [uu____11324]  in
                                           (s_body, uu____11313)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11296
                                          in
                                       mk uu____11295  in
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
                            let uu____11471 =
                              let uu____11472 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11472]  in
                            let uu____11491 =
                              mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11471 uu____11491
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11515 =
                              let uu____11524 =
                                let uu____11531 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11531
                                 in
                              [uu____11524]  in
                            let uu____11550 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11515 uu____11550
                             in
                          let uu____11553 =
                            mk
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11592 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11553, uu____11592)
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
                           let uu____11702 =
                             let uu____11703 =
                               let uu____11704 =
                                 let uu____11731 =
                                   mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11731,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11704
                                in
                             mk uu____11703  in
                           let uu____11790 =
                             mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11702, uu____11790))))

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
  fun env1  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk x = FStar_Syntax_Syntax.mk x e2.FStar_Syntax_Syntax.pos
               in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____11855 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11855]  in
            let uu____11874 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11874 with
            | (x_binders1,e21) ->
                let uu____11887 = infer env1 e1  in
                (match uu____11887 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____11904 = is_C t1  in
                       if uu____11904
                       then
                         let uu___1203_11907 = binding  in
                         let uu____11908 =
                           let uu____11911 =
                             FStar_Syntax_Subst.subst env1.subst s_e1  in
                           trans_F_ env1 t1 uu____11911  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1203_11907.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1203_11907.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11908;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1203_11907.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1203_11907.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1203_11907.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1203_11907.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env2 =
                       let uu___1206_11915 = env1  in
                       let uu____11916 =
                         FStar_TypeChecker_Env.push_bv env1.tcenv
                           (let uu___1208_11918 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1208_11918.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1208_11918.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____11916;
                         subst = (uu___1206_11915.subst);
                         tc_const = (uu___1206_11915.tc_const)
                       }  in
                     let uu____11919 = proceed env2 e21  in
                     (match uu____11919 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1215_11936 = binding  in
                            let uu____11937 =
                              star_type' env2
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1215_11936.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1215_11936.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11937;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1215_11936.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1215_11936.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1215_11936.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1215_11936.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____11940 =
                            let uu____11941 =
                              let uu____11942 =
                                let uu____11956 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1218_11973 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1218_11973.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1218_11973.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1218_11973.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1218_11973.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1218_11973.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1218_11973.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11956)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11942  in
                            mk uu____11941  in
                          let uu____11974 =
                            let uu____11975 =
                              let uu____11976 =
                                let uu____11990 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1220_12007 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1220_12007.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1220_12007.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1220_12007.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1220_12007.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1220_12007.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1220_12007.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11990)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11976  in
                            mk uu____11975  in
                          (nm_rec, uu____11940, uu____11974))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1227_12012 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1227_12012.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1227_12012.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1227_12012.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1227_12012.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1227_12012.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env2 =
                       let uu___1230_12014 = env1  in
                       let uu____12015 =
                         FStar_TypeChecker_Env.push_bv env1.tcenv
                           (let uu___1232_12017 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1232_12017.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1232_12017.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12015;
                         subst = (uu___1230_12014.subst);
                         tc_const = (uu___1230_12014.tc_const)
                       }  in
                     let uu____12018 = ensure_m env2 e21  in
                     (match uu____12018 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk env2 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12042 =
                              let uu____12043 =
                                let uu____12060 =
                                  let uu____12071 =
                                    let uu____12080 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12083 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12080, uu____12083)  in
                                  [uu____12071]  in
                                (s_e2, uu____12060)  in
                              FStar_Syntax_Syntax.Tm_app uu____12043  in
                            mk uu____12042  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12125 =
                              let uu____12126 =
                                let uu____12143 =
                                  let uu____12154 =
                                    let uu____12163 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12163)  in
                                  [uu____12154]  in
                                (s_e1, uu____12143)  in
                              FStar_Syntax_Syntax.Tm_app uu____12126  in
                            mk uu____12125  in
                          let uu____12199 =
                            let uu____12200 =
                              let uu____12201 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12201]  in
                            FStar_Syntax_Util.abs uu____12200 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12220 =
                            let uu____12221 =
                              let uu____12222 =
                                let uu____12236 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1244_12253 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1244_12253.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1244_12253.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1244_12253.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1244_12253.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1244_12253.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1244_12253.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12236)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12222  in
                            mk uu____12221  in
                          ((M t2), uu____12199, uu____12220)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1  ->
    fun e  ->
      let mn =
        let uu____12263 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            e.FStar_Syntax_Syntax.pos
           in
        N uu____12263  in
      let uu____12264 = check env1 e mn  in
      match uu____12264 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12280 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1  ->
    fun e  ->
      let mn =
        let uu____12303 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            e.FStar_Syntax_Syntax.pos
           in
        M uu____12303  in
      let uu____12304 = check env1 e mn  in
      match uu____12304 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12320 -> failwith "[check_m]: impossible"

and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm1  ->
    match nm1 with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

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
  fun env1  ->
    fun c  ->
      fun wp  ->
        (let uu____12353 =
           let uu____12355 = is_C c  in Prims.op_Negation uu____12355  in
         if uu____12353
         then
           let uu____12358 =
             let uu____12364 =
               let uu____12366 = FStar_Syntax_Print.term_to_string c  in
               FStar_Util.format1 "Not a DM4F C-type: %s" uu____12366  in
             (FStar_Errors.Error_UnexpectedDM4FType, uu____12364)  in
           FStar_Errors.raise_error uu____12358 c.FStar_Syntax_Syntax.pos
         else ());
        (let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos  in
         let uu____12380 =
           let uu____12381 = FStar_Syntax_Subst.compress c  in
           uu____12381.FStar_Syntax_Syntax.n  in
         match uu____12380 with
         | FStar_Syntax_Syntax.Tm_app (head,args) ->
             let uu____12410 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12410 with
              | (wp_head,wp_args) ->
                  ((let uu____12454 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12473 =
                           let uu____12475 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12475
                            in
                         Prims.op_Negation uu____12473)
                       in
                    if uu____12454 then failwith "mismatch" else ());
                   (let uu____12488 =
                      let uu____12489 =
                        let uu____12506 =
                          FStar_List.map2
                            (fun uu____12544  ->
                               fun uu____12545  ->
                                 match (uu____12544, uu____12545) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12607 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12607
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12616 =
                                         let uu____12618 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12618 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12616
                                       then
                                         let uu____12620 =
                                           let uu____12626 =
                                             let uu____12628 =
                                               print_implicit q  in
                                             let uu____12630 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12628 uu____12630
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12626)
                                            in
                                         FStar_Errors.log_issue
                                           head.FStar_Syntax_Syntax.pos
                                           uu____12620
                                       else ());
                                      (let uu____12636 =
                                         trans_F_ env1 arg wp_arg  in
                                       (uu____12636, q)))) args wp_args
                           in
                        (head, uu____12506)  in
                      FStar_Syntax_Syntax.Tm_app uu____12489  in
                    mk uu____12488)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12682 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12682 with
              | (binders_orig,comp1) ->
                  let uu____12689 =
                    let uu____12706 =
                      FStar_List.map
                        (fun uu____12746  ->
                           match uu____12746 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12774 = is_C h  in
                               if uu____12774
                               then
                                 let w' =
                                   let uu____12790 =
                                     let uu____12792 =
                                       FStar_Ident.string_of_id
                                         bv.FStar_Syntax_Syntax.ppname
                                        in
                                     Prims.op_Hat uu____12792 "__w'"  in
                                   let uu____12795 = star_type' env1 h  in
                                   FStar_Syntax_Syntax.gen_bv uu____12790
                                     FStar_Pervasives_Native.None uu____12795
                                    in
                                 let uu____12796 =
                                   let uu____12805 =
                                     let uu____12814 =
                                       let uu____12821 =
                                         let uu____12822 =
                                           let uu____12823 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env1 h uu____12823  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12822
                                          in
                                       (uu____12821, q)  in
                                     [uu____12814]  in
                                   (w', q) :: uu____12805  in
                                 (w', uu____12796)
                               else
                                 (let x =
                                    let uu____12857 =
                                      let uu____12859 =
                                        FStar_Ident.string_of_id
                                          bv.FStar_Syntax_Syntax.ppname
                                         in
                                      Prims.op_Hat uu____12859 "__x"  in
                                    let uu____12862 = star_type' env1 h  in
                                    FStar_Syntax_Syntax.gen_bv uu____12857
                                      FStar_Pervasives_Native.None
                                      uu____12862
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12706  in
                  (match uu____12689 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____12935 =
                           let uu____12938 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12938
                            in
                         FStar_Syntax_Subst.subst_comp uu____12935 comp1  in
                       let app =
                         let uu____12942 =
                           let uu____12943 =
                             let uu____12960 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____12979 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____12980 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12979, uu____12980)) bvs
                                in
                             (wp, uu____12960)  in
                           FStar_Syntax_Syntax.Tm_app uu____12943  in
                         mk uu____12942  in
                       let comp3 =
                         let uu____12995 = type_of_comp comp2  in
                         let uu____12996 = is_monadic_comp comp2  in
                         trans_G env1 uu____12995 uu____12996 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____12999,uu____13000) ->
             trans_F_ env1 e wp
         | uu____13041 -> failwith "impossible trans_F_")

and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env1  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____13049 =
              let uu____13050 = star_type' env1 h  in
              let uu____13053 =
                let uu____13064 =
                  let uu____13073 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13073)  in
                [uu____13064]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13050;
                FStar_Syntax_Syntax.effect_args = uu____13053;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13049
          else
            (let uu____13099 = trans_F_ env1 h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13099)

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
  fun env1  ->
    fun t  ->
      let uu____13120 = n env1.tcenv t  in star_type' env1 uu____13120
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1  ->
    fun t  -> let uu____13140 = n env1.tcenv t  in check_n env1 uu____13140
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun wp  ->
        let uu____13157 = n env1.tcenv c  in
        let uu____13158 = n env1.tcenv wp  in
        trans_F_ env1 uu____13157 uu____13158
  
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun env1  ->
      fun t  ->
        (let uu____13178 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED")  in
         if uu____13178
         then
           let uu____13182 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s
             uu____13182
         else ());
        (let uu____13187 = FStar_TypeChecker_TcTerm.tc_term env1 t  in
         match uu____13187 with
         | (t',uu____13195,uu____13196) ->
             ((let uu____13198 =
                 FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED")
                  in
               if uu____13198
               then
                 let uu____13202 = FStar_Syntax_Print.term_to_string t'  in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____13202
               else ());
              t'))
  
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env1  ->
    fun ed  ->
      let uu____13238 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature)
         in
      match uu____13238 with
      | (effect_binders_un,signature_un) ->
          let uu____13259 =
            FStar_TypeChecker_TcTerm.tc_tparams env1 effect_binders_un  in
          (match uu____13259 with
           | (effect_binders,env2,uu____13278) ->
               let uu____13279 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env2 signature_un
                  in
               (match uu____13279 with
                | (signature,uu____13295) ->
                    let raise_error uu____13311 =
                      match uu____13311 with
                      | (e,err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos
                       in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____13347  ->
                           match uu____13347 with
                           | (bv,qual) ->
                               let uu____13366 =
                                 let uu___1370_13367 = bv  in
                                 let uu____13368 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env2 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1370_13367.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1370_13367.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____13368
                                 }  in
                               (uu____13366, qual)) effect_binders
                       in
                    let uu____13373 =
                      let uu____13380 =
                        let uu____13381 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____13381.FStar_Syntax_Syntax.n  in
                      match uu____13380 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____13391)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____13423 ->
                          raise_error
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature")
                       in
                    (match uu____13373 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____13449 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____13449
                           then
                             let uu____13452 =
                               let uu____13455 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               FStar_Pervasives_Native.Some uu____13455  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____13452
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check env3 other_binders t =
                           let subst =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders)
                              in
                           let t1 = FStar_Syntax_Subst.subst subst t  in
                           let uu____13503 =
                             FStar_TypeChecker_TcTerm.tc_term env3 t1  in
                           match uu____13503 with
                           | (t2,comp,uu____13516) -> (t2, comp)  in
                         let mk x =
                           FStar_Syntax_Syntax.mk x
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____13525 =
                           let uu____13530 =
                             let uu____13531 =
                               let uu____13540 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____13540
                                 FStar_Util.must
                                in
                             FStar_All.pipe_right uu____13531
                               FStar_Pervasives_Native.snd
                              in
                           open_and_check env2 [] uu____13530  in
                         (match uu____13525 with
                          | (repr,_comp) ->
                              ((let uu____13586 =
                                  FStar_TypeChecker_Env.debug env2
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____13586
                                then
                                  let uu____13590 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____13590
                                else ());
                               (let ed_range =
                                  FStar_TypeChecker_Env.get_range env2  in
                                let dmff_env =
                                  empty env2
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env2 FStar_Range.dummyRange)
                                   in
                                let wp_type = star_type dmff_env repr  in
                                let uu____13598 =
                                  recheck_debug "*" env2 wp_type  in
                                let wp_a =
                                  let uu____13601 =
                                    let uu____13602 =
                                      let uu____13603 =
                                        let uu____13620 =
                                          let uu____13631 =
                                            let uu____13640 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____13643 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____13640, uu____13643)  in
                                          [uu____13631]  in
                                        (wp_type, uu____13620)  in
                                      FStar_Syntax_Syntax.Tm_app uu____13603
                                       in
                                    mk uu____13602  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env2
                                    uu____13601
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____13691 =
                                      let uu____13698 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____13698)  in
                                    let uu____13704 =
                                      let uu____13713 =
                                        let uu____13720 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a
                                           in
                                        FStar_All.pipe_right uu____13720
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____13713]  in
                                    uu____13691 :: uu____13704  in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders
                                     in
                                  mk
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker))
                                   in
                                let uu____13757 =
                                  recheck_debug
                                    "turned into the effect signature" env2
                                    effect_signature
                                   in
                                let sigelts = FStar_Util.mk_ref []  in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name  in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env3 = get_env dmff_env1  in
                                  let uu____13823 = item  in
                                  match uu____13823 with
                                  | (u_item,item1) ->
                                      let uu____13838 =
                                        open_and_check env3 other_binders
                                          item1
                                         in
                                      (match uu____13838 with
                                       | (item2,item_comp) ->
                                           ((let uu____13854 =
                                               let uu____13856 =
                                                 FStar_TypeChecker_Common.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____13856
                                                in
                                             if uu____13854
                                             then
                                               let uu____13859 =
                                                 let uu____13865 =
                                                   let uu____13867 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____13869 =
                                                     FStar_TypeChecker_Common.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____13867 uu____13869
                                                    in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____13865)
                                                  in
                                               FStar_Errors.raise_err
                                                 uu____13859
                                             else ());
                                            (let uu____13875 =
                                               star_expr dmff_env1 item2  in
                                             match uu____13875 with
                                             | (item_t,item_wp,item_elab) ->
                                                 let uu____13893 =
                                                   recheck_debug "*" env3
                                                     item_wp
                                                    in
                                                 let uu____13895 =
                                                   recheck_debug "_" env3
                                                     item_elab
                                                    in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab))))
                                   in
                                let uu____13897 =
                                  let uu____13906 =
                                    let uu____13911 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr
                                       in
                                    FStar_All.pipe_right uu____13911
                                      FStar_Util.must
                                     in
                                  elaborate_and_star dmff_env [] uu____13906
                                   in
                                match uu____13897 with
                                | (dmff_env1,uu____13939,bind_wp,bind_elab)
                                    ->
                                    let uu____13942 =
                                      let uu____13951 =
                                        let uu____13956 =
                                          FStar_All.pipe_right ed
                                            FStar_Syntax_Util.get_return_repr
                                           in
                                        FStar_All.pipe_right uu____13956
                                          FStar_Util.must
                                         in
                                      elaborate_and_star dmff_env1 []
                                        uu____13951
                                       in
                                    (match uu____13942 with
                                     | (dmff_env2,uu____13984,return_wp,return_elab)
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
                                           let uu____13993 =
                                             let uu____13994 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____13994.FStar_Syntax_Syntax.n
                                              in
                                           match uu____13993 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____14052 =
                                                 let uu____14071 =
                                                   let uu____14076 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____14076
                                                    in
                                                 match uu____14071 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____14158 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____14052 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____14212 =
                                                        get_env dmff_env2  in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____14212
                                                        [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____14235 =
                                                          let uu____14236 =
                                                            let uu____14253 =
                                                              let uu____14264
                                                                =
                                                                let uu____14273
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11)
                                                                   in
                                                                let uu____14278
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____14273,
                                                                  uu____14278)
                                                                 in
                                                              [uu____14264]
                                                               in
                                                            (wp_type,
                                                              uu____14253)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____14236
                                                           in
                                                        mk uu____14235  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1
                                                       in
                                                    let uu____14314 =
                                                      let uu____14323 =
                                                        let uu____14324 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____14324
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____14323
                                                       in
                                                    (match uu____14314 with
                                                     | (bs1,body2,what') ->
                                                         let fail uu____14347
                                                           =
                                                           let error_msg =
                                                             let uu____14350
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2
                                                                in
                                                             let uu____14352
                                                               =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                    -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.string_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____14350
                                                               uu____14352
                                                              in
                                                           raise_error
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg)
                                                            in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                                -> fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____14362
                                                                   =
                                                                   let uu____14364
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect
                                                                     in
                                                                   Prims.op_Negation
                                                                    uu____14364
                                                                    in
                                                                 if
                                                                   uu____14362
                                                                 then fail ()
                                                                 else ());
                                                                (let uu____14369
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt 
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env2
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0
                                                                     in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env2 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail ())
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   uu____14369
                                                                   (fun
                                                                    uu____14387
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
                                                             let uu____14397
                                                               =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp
                                                                in
                                                             let uu____14398
                                                               =
                                                               let uu____14399
                                                                 =
                                                                 let uu____14408
                                                                   =
                                                                   FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'
                                                                    in
                                                                 (uu____14408,
                                                                   FStar_Pervasives_Native.None)
                                                                  in
                                                               [uu____14399]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu____14397
                                                               uu____14398
                                                               ed_range
                                                              in
                                                           let uu____14443 =
                                                             let uu____14444
                                                               =
                                                               let uu____14453
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp
                                                                  in
                                                               [uu____14453]
                                                                in
                                                             b11 ::
                                                               uu____14444
                                                              in
                                                           let uu____14478 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what
                                                              in
                                                           FStar_Syntax_Util.abs
                                                             uu____14443
                                                             uu____14478
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____14481 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let return_wp1 =
                                           let uu____14489 =
                                             let uu____14490 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____14490.FStar_Syntax_Syntax.n
                                              in
                                           match uu____14489 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____14548 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____14548
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____14569 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return")
                                            in
                                         let bind_wp1 =
                                           let uu____14577 =
                                             let uu____14578 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____14578.FStar_Syntax_Syntax.n
                                              in
                                           match uu____14577 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None
                                                  in
                                               let uu____14612 =
                                                 let uu____14613 =
                                                   let uu____14622 =
                                                     let uu____14629 =
                                                       mk
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____14629
                                                      in
                                                   [uu____14622]  in
                                                 FStar_List.append
                                                   uu____14613 binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____14612 body what
                                           | uu____14648 ->
                                               raise_error
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
                                             (let uu____14678 =
                                                let uu____14679 =
                                                  let uu____14680 =
                                                    let uu____14697 =
                                                      let uu____14708 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      FStar_Pervasives_Native.snd
                                                        uu____14708
                                                       in
                                                    (t, uu____14697)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____14680
                                                   in
                                                mk uu____14679  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____14678)
                                            in
                                         let rec apply_last f l =
                                           match l with
                                           | [] ->
                                               failwith
                                                 "impossible: empty path.."
                                           | a2::[] ->
                                               let uu____14766 = f a2  in
                                               [uu____14766]
                                           | x::xs ->
                                               let uu____14777 =
                                                 apply_last f xs  in
                                               x :: uu____14777
                                            in
                                         let register maybe_admit name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname
                                              in
                                           let p' =
                                             apply_last
                                               (fun s  ->
                                                  Prims.op_Hat "__"
                                                    (Prims.op_Hat s
                                                       (Prims.op_Hat
                                                          "_eff_override_"
                                                          name))) p
                                              in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               ed_range
                                              in
                                           let uu____14818 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env2 l'
                                              in
                                           match uu____14818 with
                                           | FStar_Pervasives_Native.Some
                                               (_us,_t) ->
                                               ((let uu____14848 =
                                                   FStar_Options.debug_any ()
                                                    in
                                                 if uu____14848
                                                 then
                                                   let uu____14851 =
                                                     FStar_Ident.string_of_lid
                                                       l'
                                                      in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____14851
                                                 else ());
                                                (let uu____14856 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____14856))
                                           | FStar_Pervasives_Native.None  ->
                                               let uu____14865 =
                                                 let uu____14870 =
                                                   mk_lid name  in
                                                 let uu____14871 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None
                                                    in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env2 uu____14870
                                                   uu____14871
                                                  in
                                               (match uu____14865 with
                                                | (sigelt,fv) ->
                                                    let sigelt1 =
                                                      if maybe_admit
                                                      then
                                                        let uu___1544_14876 =
                                                          sigelt  in
                                                        {
                                                          FStar_Syntax_Syntax.sigel
                                                            =
                                                            (uu___1544_14876.FStar_Syntax_Syntax.sigel);
                                                          FStar_Syntax_Syntax.sigrng
                                                            =
                                                            (uu___1544_14876.FStar_Syntax_Syntax.sigrng);
                                                          FStar_Syntax_Syntax.sigquals
                                                            =
                                                            (uu___1544_14876.FStar_Syntax_Syntax.sigquals);
                                                          FStar_Syntax_Syntax.sigmeta
                                                            =
                                                            (let uu___1546_14878
                                                               =
                                                               sigelt.FStar_Syntax_Syntax.sigmeta
                                                                in
                                                             {
                                                               FStar_Syntax_Syntax.sigmeta_active
                                                                 =
                                                                 (uu___1546_14878.FStar_Syntax_Syntax.sigmeta_active);
                                                               FStar_Syntax_Syntax.sigmeta_fact_db_ids
                                                                 =
                                                                 (uu___1546_14878.FStar_Syntax_Syntax.sigmeta_fact_db_ids);
                                                               FStar_Syntax_Syntax.sigmeta_admit
                                                                 = true
                                                             });
                                                          FStar_Syntax_Syntax.sigattrs
                                                            =
                                                            (uu___1544_14876.FStar_Syntax_Syntax.sigattrs);
                                                          FStar_Syntax_Syntax.sigopts
                                                            =
                                                            (uu___1544_14876.FStar_Syntax_Syntax.sigopts)
                                                        }
                                                      else sigelt  in
                                                    ((let uu____14883 =
                                                        let uu____14886 =
                                                          FStar_ST.op_Bang
                                                            sigelts
                                                           in
                                                        sigelt1 ::
                                                          uu____14886
                                                         in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____14883);
                                                     fv))
                                            in
                                         let register_admit = register true
                                            in
                                         let register1 = register false  in
                                         let lift_from_pure_wp1 =
                                           register1 "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let mk_sigelt se =
                                           let uu___1555_14969 =
                                             FStar_Syntax_Syntax.mk_sigelt se
                                              in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (uu___1555_14969.FStar_Syntax_Syntax.sigel);
                                             FStar_Syntax_Syntax.sigrng =
                                               ed_range;
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___1555_14969.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___1555_14969.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___1555_14969.FStar_Syntax_Syntax.sigattrs);
                                             FStar_Syntax_Syntax.sigopts =
                                               (uu___1555_14969.FStar_Syntax_Syntax.sigopts)
                                           }  in
                                         let return_wp2 =
                                           register1 "return_wp" return_wp1
                                            in
                                         ((let uu____14973 =
                                             let uu____14976 =
                                               mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       FStar_Pervasives_Native.None))
                                                in
                                             let uu____14978 =
                                               FStar_ST.op_Bang sigelts  in
                                             uu____14976 :: uu____14978  in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____14973);
                                          (let return_elab1 =
                                             register_admit "return_elab"
                                               return_elab
                                              in
                                           (let uu____15030 =
                                              let uu____15033 =
                                                mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions)
                                                 in
                                              let uu____15034 =
                                                FStar_ST.op_Bang sigelts  in
                                              uu____15033 :: uu____15034  in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____15030);
                                           (let bind_wp2 =
                                              register1 "bind_wp" bind_wp1
                                               in
                                            (let uu____15086 =
                                               let uu____15089 =
                                                 mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         FStar_Pervasives_Native.None))
                                                  in
                                               let uu____15091 =
                                                 FStar_ST.op_Bang sigelts  in
                                               uu____15089 :: uu____15091  in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____15086);
                                            (let bind_elab1 =
                                               register_admit "bind_elab"
                                                 bind_elab
                                                in
                                             (let uu____15143 =
                                                let uu____15146 =
                                                  mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions)
                                                   in
                                                let uu____15147 =
                                                  FStar_ST.op_Bang sigelts
                                                   in
                                                uu____15146 :: uu____15147
                                                 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____15143);
                                             (let uu____15196 =
                                                FStar_List.fold_left
                                                  (fun uu____15236  ->
                                                     fun action  ->
                                                       match uu____15236 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params
                                                              in
                                                           let uu____15257 =
                                                             let uu____15264
                                                               =
                                                               get_env
                                                                 dmff_env3
                                                                in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____15264
                                                               params_un
                                                              in
                                                           (match uu____15257
                                                            with
                                                            | (action_params,env',uu____15273)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____15299
                                                                     ->
                                                                    match uu____15299
                                                                    with
                                                                    | 
                                                                    (bv,qual)
                                                                    ->
                                                                    let uu____15318
                                                                    =
                                                                    let uu___1577_15319
                                                                    = bv  in
                                                                    let uu____15320
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___1577_15319.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1577_15319.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____15320
                                                                    }  in
                                                                    (uu____15318,
                                                                    qual))
                                                                    action_params
                                                                   in
                                                                let dmff_env'
                                                                  =
                                                                  set_env
                                                                    dmff_env3
                                                                    env'
                                                                   in
                                                                let uu____15326
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn))
                                                                   in
                                                                (match uu____15326
                                                                 with
                                                                 | (dmff_env4,action_t,action_wp,action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    let uu____15347
                                                                    =
                                                                    FStar_Ident.ident_of_lid
                                                                    action.FStar_Syntax_Syntax.action_name
                                                                     in
                                                                    FStar_Ident.string_of_id
                                                                    uu____15347
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
                                                                    uu____15366
                                                                    ->
                                                                    let uu____15367
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1
                                                                     in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____15367
                                                                     in
                                                                    ((
                                                                    let uu____15371
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "ED")  in
                                                                    if
                                                                    uu____15371
                                                                    then
                                                                    let uu____15376
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un
                                                                     in
                                                                    let uu____15379
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2
                                                                     in
                                                                    let uu____15382
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____15384
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2
                                                                     in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____15376
                                                                    uu____15379
                                                                    uu____15382
                                                                    uu____15384
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register1
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2
                                                                     in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register1
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2
                                                                     in
                                                                    let uu____15393
                                                                    =
                                                                    let uu____15396
                                                                    =
                                                                    let uu___1599_15397
                                                                    = action
                                                                     in
                                                                    let uu____15398
                                                                    =
                                                                    apply_close
                                                                    action_elab3
                                                                     in
                                                                    let uu____15399
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1599_15397.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1599_15397.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___1599_15397.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____15398;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____15399
                                                                    }  in
                                                                    uu____15396
                                                                    ::
                                                                    actions
                                                                     in
                                                                    (dmff_env4,
                                                                    uu____15393))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____15196 with
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
                                                      let uu____15443 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____15450 =
                                                        let uu____15459 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____15459]  in
                                                      uu____15443 ::
                                                        uu____15450
                                                       in
                                                    let uu____15484 =
                                                      let uu____15487 =
                                                        let uu____15488 =
                                                          let uu____15489 =
                                                            let uu____15506 =
                                                              let uu____15517
                                                                =
                                                                let uu____15526
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____15529
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____15526,
                                                                  uu____15529)
                                                                 in
                                                              [uu____15517]
                                                               in
                                                            (repr,
                                                              uu____15506)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____15489
                                                           in
                                                        mk uu____15488  in
                                                      let uu____15565 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      trans_F dmff_env3
                                                        uu____15487
                                                        uu____15565
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____15484
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  let uu____15566 =
                                                    recheck_debug "FC" env2
                                                      repr1
                                                     in
                                                  let repr2 =
                                                    register1 "repr" repr1
                                                     in
                                                  let uu____15570 =
                                                    let uu____15579 =
                                                      let uu____15580 =
                                                        let uu____15583 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____15583
                                                         in
                                                      uu____15580.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____15579 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow,uu____15597)
                                                        ->
                                                        let uu____15634 =
                                                          let uu____15655 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow
                                                             in
                                                          match uu____15655
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____15723 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____15634
                                                         with
                                                         | (type_param1,effect_param1,arrow1)
                                                             ->
                                                             let uu____15788
                                                               =
                                                               let uu____15789
                                                                 =
                                                                 let uu____15792
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow1
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____15792
                                                                  in
                                                               uu____15789.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____15788
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____15825
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____15825
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____15840
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____15871
                                                                     ->
                                                                    match uu____15871
                                                                    with
                                                                    | 
                                                                    (bv,uu____15880)
                                                                    ->
                                                                    let uu____15885
                                                                    =
                                                                    let uu____15887
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15887
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15885
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____15840
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
                                                                    let uu____15979
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____15979
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____15989
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____16000
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____16000
                                                                     in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                     in
                                                                    let uu____16010
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____16013
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    (uu____16010,
                                                                    uu____16013)))
                                                              | uu____16028
                                                                  ->
                                                                  let uu____16029
                                                                    =
                                                                    let uu____16035
                                                                    =
                                                                    let uu____16037
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____16037
                                                                     in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____16035)
                                                                     in
                                                                  raise_error
                                                                    uu____16029))
                                                    | uu____16049 ->
                                                        let uu____16050 =
                                                          let uu____16056 =
                                                            let uu____16058 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type
                                                               in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____16058
                                                             in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____16056)
                                                           in
                                                        raise_error
                                                          uu____16050
                                                     in
                                                  (match uu____15570 with
                                                   | (pre,post) ->
                                                       ((let uu____16091 =
                                                           register1 "pre"
                                                             pre
                                                            in
                                                         ());
                                                        (let uu____16094 =
                                                           register1 "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____16097 =
                                                           register1 "wp"
                                                             wp_type
                                                            in
                                                         ());
                                                        (let ed_combs =
                                                           match ed.FStar_Syntax_Syntax.combinators
                                                           with
                                                           | FStar_Syntax_Syntax.DM4F_eff
                                                               combs ->
                                                               let uu____16101
                                                                 =
                                                                 let uu___1657_16102
                                                                   = combs
                                                                    in
                                                                 let uu____16103
                                                                   =
                                                                   let uu____16104
                                                                    =
                                                                    apply_close
                                                                    return_wp2
                                                                     in
                                                                   ([],
                                                                    uu____16104)
                                                                    in
                                                                 let uu____16111
                                                                   =
                                                                   let uu____16112
                                                                    =
                                                                    apply_close
                                                                    bind_wp2
                                                                     in
                                                                   ([],
                                                                    uu____16112)
                                                                    in
                                                                 let uu____16119
                                                                   =
                                                                   let uu____16122
                                                                    =
                                                                    let uu____16123
                                                                    =
                                                                    apply_close
                                                                    repr2  in
                                                                    ([],
                                                                    uu____16123)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16122
                                                                    in
                                                                 let uu____16130
                                                                   =
                                                                   let uu____16133
                                                                    =
                                                                    let uu____16134
                                                                    =
                                                                    apply_close
                                                                    return_elab1
                                                                     in
                                                                    ([],
                                                                    uu____16134)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16133
                                                                    in
                                                                 let uu____16141
                                                                   =
                                                                   let uu____16144
                                                                    =
                                                                    let uu____16145
                                                                    =
                                                                    apply_close
                                                                    bind_elab1
                                                                     in
                                                                    ([],
                                                                    uu____16145)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16144
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.ret_wp
                                                                    =
                                                                    uu____16103;
                                                                   FStar_Syntax_Syntax.bind_wp
                                                                    =
                                                                    uu____16111;
                                                                   FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    (uu___1657_16102.FStar_Syntax_Syntax.stronger);
                                                                   FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    (uu___1657_16102.FStar_Syntax_Syntax.if_then_else);
                                                                   FStar_Syntax_Syntax.ite_wp
                                                                    =
                                                                    (uu___1657_16102.FStar_Syntax_Syntax.ite_wp);
                                                                   FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    (uu___1657_16102.FStar_Syntax_Syntax.close_wp);
                                                                   FStar_Syntax_Syntax.trivial
                                                                    =
                                                                    (uu___1657_16102.FStar_Syntax_Syntax.trivial);
                                                                   FStar_Syntax_Syntax.repr
                                                                    =
                                                                    uu____16119;
                                                                   FStar_Syntax_Syntax.return_repr
                                                                    =
                                                                    uu____16130;
                                                                   FStar_Syntax_Syntax.bind_repr
                                                                    =
                                                                    uu____16141
                                                                 }  in
                                                               FStar_Syntax_Syntax.DM4F_eff
                                                                 uu____16101
                                                           | uu____16152 ->
                                                               failwith
                                                                 "Impossible! For a DM4F effect combinators must be in DM4f_eff"
                                                            in
                                                         let ed1 =
                                                           let uu___1661_16155
                                                             = ed  in
                                                           let uu____16156 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____16157 =
                                                             let uu____16158
                                                               =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature
                                                                in
                                                             ([],
                                                               uu____16158)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___1661_16155.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___1661_16155.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___1661_16155.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____16156;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____16157;
                                                             FStar_Syntax_Syntax.combinators
                                                               = ed_combs;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___1661_16155.FStar_Syntax_Syntax.eff_attrs)
                                                           }  in
                                                         let uu____16165 =
                                                           gen_wps_for_free
                                                             env2
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____16165
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____16183
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env2
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____16183
                                                               then
                                                                 let uu____16187
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____16187
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
                                                                    let uu____16207
                                                                    =
                                                                    let uu____16210
                                                                    =
                                                                    let uu____16211
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    ([],
                                                                    uu____16211)
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____16210
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
                                                                    uu____16207;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    }  in
                                                                   let uu____16218
                                                                    =
                                                                    mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure)
                                                                     in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____16218
                                                                 else
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let uu____16221
                                                                 =
                                                                 let uu____16224
                                                                   =
                                                                   let uu____16227
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____16227
                                                                    in
                                                                 FStar_List.append
                                                                   uu____16224
                                                                   sigelts'
                                                                  in
                                                               (uu____16221,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))
  