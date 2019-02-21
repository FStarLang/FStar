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
              let uu___12_127 = a  in
              let uu____128 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___12_127.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___12_127.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____128
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____141 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____141
             then
               (d "Elaborating extra WP combinators";
                (let uu____147 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____147))
             else ());
            (let rec collect_binders t =
               let uu____166 =
                 let uu____167 =
                   let uu____170 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____170
                    in
                 uu____167.FStar_Syntax_Syntax.n  in
               match uu____166 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____205) -> t1
                     | uu____214 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____216 = collect_binders rest  in
                   FStar_List.append bs uu____216
               | FStar_Syntax_Syntax.Tm_type uu____231 -> []
               | uu____238 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____265 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____265 FStar_Syntax_Util.name_binders
                in
             (let uu____291 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____291
              then
                let uu____295 =
                  let uu____297 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____297  in
                d uu____295
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____335 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____335 with
                | (sigelt,fv) ->
                    ((let uu____343 =
                        let uu____346 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____346
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____343);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____470  ->
                     match uu____470 with
                     | (t,b) ->
                         let uu____484 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____484))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____523 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____523))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____557 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____557)
                 in
              let uu____560 =
                let uu____577 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____602 =
                        let uu____605 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____605  in
                      FStar_Syntax_Util.arrow gamma uu____602  in
                    let uu____606 =
                      let uu____607 =
                        let uu____616 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____623 =
                          let uu____632 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____632]  in
                        uu____616 :: uu____623  in
                      FStar_List.append binders uu____607  in
                    FStar_Syntax_Util.abs uu____606 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____663 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____664 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____663, uu____664)  in
                match uu____577 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____706 =
                        let uu____707 =
                          let uu____724 =
                            let uu____735 =
                              FStar_List.map
                                (fun uu____757  ->
                                   match uu____757 with
                                   | (bv,uu____769) ->
                                       let uu____774 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____775 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____774, uu____775)) binders
                               in
                            let uu____777 =
                              let uu____784 =
                                let uu____789 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____790 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____789, uu____790)  in
                              let uu____792 =
                                let uu____799 =
                                  let uu____804 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____804)  in
                                [uu____799]  in
                              uu____784 :: uu____792  in
                            FStar_List.append uu____735 uu____777  in
                          (fv, uu____724)  in
                        FStar_Syntax_Syntax.Tm_app uu____707  in
                      mk1 uu____706  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____560 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____877 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____877
                       in
                    let ret1 =
                      let uu____882 =
                        let uu____883 =
                          let uu____886 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____886  in
                        FStar_Syntax_Util.residual_tot uu____883  in
                      FStar_Pervasives_Native.Some uu____882  in
                    let body =
                      let uu____890 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____890 ret1  in
                    let uu____893 =
                      let uu____894 = mk_all_implicit binders  in
                      let uu____901 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____894 uu____901  in
                    FStar_Syntax_Util.abs uu____893 body ret1  in
                  let c_pure1 =
                    let uu____939 = mk_lid "pure"  in
                    register env1 uu____939 c_pure  in
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
                      let uu____949 =
                        let uu____950 =
                          let uu____951 =
                            let uu____960 =
                              let uu____967 =
                                let uu____968 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____968
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____967  in
                            [uu____960]  in
                          let uu____981 =
                            let uu____984 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____984  in
                          FStar_Syntax_Util.arrow uu____951 uu____981  in
                        mk_gctx uu____950  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____949
                       in
                    let r =
                      let uu____987 =
                        let uu____988 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____988  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____987
                       in
                    let ret1 =
                      let uu____993 =
                        let uu____994 =
                          let uu____997 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____997  in
                        FStar_Syntax_Util.residual_tot uu____994  in
                      FStar_Pervasives_Native.Some uu____993  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____1007 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____1010 =
                          let uu____1021 =
                            let uu____1024 =
                              let uu____1025 =
                                let uu____1026 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____1026
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1025  in
                            [uu____1024]  in
                          FStar_List.append gamma_as_args uu____1021  in
                        FStar_Syntax_Util.mk_app uu____1007 uu____1010  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____1029 =
                      let uu____1030 = mk_all_implicit binders  in
                      let uu____1037 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____1030 uu____1037  in
                    FStar_Syntax_Util.abs uu____1029 outer_body ret1  in
                  let c_app1 =
                    let uu____1089 = mk_lid "app"  in
                    register env1 uu____1089 c_app  in
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
                      let uu____1101 =
                        let uu____1110 =
                          let uu____1117 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1117  in
                        [uu____1110]  in
                      let uu____1130 =
                        let uu____1133 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1133  in
                      FStar_Syntax_Util.arrow uu____1101 uu____1130  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1137 =
                        let uu____1138 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1138  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1137
                       in
                    let ret1 =
                      let uu____1143 =
                        let uu____1144 =
                          let uu____1147 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1147  in
                        FStar_Syntax_Util.residual_tot uu____1144  in
                      FStar_Pervasives_Native.Some uu____1143  in
                    let uu____1148 =
                      let uu____1149 = mk_all_implicit binders  in
                      let uu____1156 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1149 uu____1156  in
                    let uu____1207 =
                      let uu____1210 =
                        let uu____1221 =
                          let uu____1224 =
                            let uu____1225 =
                              let uu____1236 =
                                let uu____1239 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1239]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1236
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1225  in
                          let uu____1248 =
                            let uu____1251 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1251]  in
                          uu____1224 :: uu____1248  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1221
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1210  in
                    FStar_Syntax_Util.abs uu____1148 uu____1207 ret1  in
                  let c_lift11 =
                    let uu____1261 = mk_lid "lift1"  in
                    register env1 uu____1261 c_lift1  in
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
                      let uu____1275 =
                        let uu____1284 =
                          let uu____1291 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1291  in
                        let uu____1292 =
                          let uu____1301 =
                            let uu____1308 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1308  in
                          [uu____1301]  in
                        uu____1284 :: uu____1292  in
                      let uu____1327 =
                        let uu____1330 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1330  in
                      FStar_Syntax_Util.arrow uu____1275 uu____1327  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1334 =
                        let uu____1335 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1335  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1334
                       in
                    let a2 =
                      let uu____1338 =
                        let uu____1339 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1339  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1338
                       in
                    let ret1 =
                      let uu____1344 =
                        let uu____1345 =
                          let uu____1348 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1348  in
                        FStar_Syntax_Util.residual_tot uu____1345  in
                      FStar_Pervasives_Native.Some uu____1344  in
                    let uu____1349 =
                      let uu____1350 = mk_all_implicit binders  in
                      let uu____1357 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1350 uu____1357  in
                    let uu____1422 =
                      let uu____1425 =
                        let uu____1436 =
                          let uu____1439 =
                            let uu____1440 =
                              let uu____1451 =
                                let uu____1454 =
                                  let uu____1455 =
                                    let uu____1466 =
                                      let uu____1469 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1469]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1466
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1455
                                   in
                                let uu____1478 =
                                  let uu____1481 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1481]  in
                                uu____1454 :: uu____1478  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1451
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1440  in
                          let uu____1490 =
                            let uu____1493 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1493]  in
                          uu____1439 :: uu____1490  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1436
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1425  in
                    FStar_Syntax_Util.abs uu____1349 uu____1422 ret1  in
                  let c_lift21 =
                    let uu____1503 = mk_lid "lift2"  in
                    register env1 uu____1503 c_lift2  in
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
                      let uu____1515 =
                        let uu____1524 =
                          let uu____1531 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1531  in
                        [uu____1524]  in
                      let uu____1544 =
                        let uu____1547 =
                          let uu____1548 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1548  in
                        FStar_Syntax_Syntax.mk_Total uu____1547  in
                      FStar_Syntax_Util.arrow uu____1515 uu____1544  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1554 =
                        let uu____1555 =
                          let uu____1558 =
                            let uu____1559 =
                              let uu____1568 =
                                let uu____1575 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1575
                                 in
                              [uu____1568]  in
                            let uu____1588 =
                              let uu____1591 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1591  in
                            FStar_Syntax_Util.arrow uu____1559 uu____1588  in
                          mk_ctx uu____1558  in
                        FStar_Syntax_Util.residual_tot uu____1555  in
                      FStar_Pervasives_Native.Some uu____1554  in
                    let e1 =
                      let uu____1593 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1593
                       in
                    let body =
                      let uu____1598 =
                        let uu____1599 =
                          let uu____1608 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1608]  in
                        FStar_List.append gamma uu____1599  in
                      let uu____1633 =
                        let uu____1636 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1639 =
                          let uu____1650 =
                            let uu____1651 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1651  in
                          let uu____1652 = args_of_binders1 gamma  in
                          uu____1650 :: uu____1652  in
                        FStar_Syntax_Util.mk_app uu____1636 uu____1639  in
                      FStar_Syntax_Util.abs uu____1598 uu____1633 ret1  in
                    let uu____1655 =
                      let uu____1656 = mk_all_implicit binders  in
                      let uu____1663 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1656 uu____1663  in
                    FStar_Syntax_Util.abs uu____1655 body ret1  in
                  let c_push1 =
                    let uu____1708 = mk_lid "push"  in
                    register env1 uu____1708 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1735 =
                        let uu____1736 =
                          let uu____1753 = args_of_binders1 binders  in
                          (c, uu____1753)  in
                        FStar_Syntax_Syntax.Tm_app uu____1736  in
                      mk1 uu____1735
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1782 =
                        let uu____1783 =
                          let uu____1792 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1799 =
                            let uu____1808 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1808]  in
                          uu____1792 :: uu____1799  in
                        let uu____1833 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1783 uu____1833  in
                      FStar_Syntax_Syntax.mk_Total uu____1782  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1838 =
                      let uu____1839 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1839  in
                    let uu____1854 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1859 =
                        let uu____1862 =
                          let uu____1873 =
                            let uu____1876 =
                              let uu____1877 =
                                let uu____1888 =
                                  let uu____1897 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1897  in
                                [uu____1888]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1877  in
                            [uu____1876]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1873
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1862  in
                      FStar_Syntax_Util.ascribe uu____1859
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1838 uu____1854
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1941 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1941 wp_if_then_else  in
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
                      let uu____1958 =
                        let uu____1969 =
                          let uu____1972 =
                            let uu____1973 =
                              let uu____1984 =
                                let uu____1987 =
                                  let uu____1988 =
                                    let uu____1999 =
                                      let uu____2008 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2008
                                       in
                                    [uu____1999]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1988
                                   in
                                [uu____1987]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1984
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1973  in
                          let uu____2033 =
                            let uu____2036 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2036]  in
                          uu____1972 :: uu____2033  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1969
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1958  in
                    let uu____2045 =
                      let uu____2046 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2046  in
                    FStar_Syntax_Util.abs uu____2045 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____2062 = mk_lid "wp_assert"  in
                    register env1 uu____2062 wp_assert  in
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
                      let uu____2079 =
                        let uu____2090 =
                          let uu____2093 =
                            let uu____2094 =
                              let uu____2105 =
                                let uu____2108 =
                                  let uu____2109 =
                                    let uu____2120 =
                                      let uu____2129 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____2129
                                       in
                                    [uu____2120]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____2109
                                   in
                                [uu____2108]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____2105
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2094  in
                          let uu____2154 =
                            let uu____2157 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2157]  in
                          uu____2093 :: uu____2154  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2090
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2079  in
                    let uu____2166 =
                      let uu____2167 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2167  in
                    FStar_Syntax_Util.abs uu____2166 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2183 = mk_lid "wp_assume"  in
                    register env1 uu____2183 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2196 =
                        let uu____2205 =
                          let uu____2212 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2212  in
                        [uu____2205]  in
                      let uu____2225 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2196 uu____2225  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2233 =
                        let uu____2244 =
                          let uu____2247 =
                            let uu____2248 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2248  in
                          let uu____2267 =
                            let uu____2270 =
                              let uu____2271 =
                                let uu____2282 =
                                  let uu____2285 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2285]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2282
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2271  in
                            [uu____2270]  in
                          uu____2247 :: uu____2267  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2244
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2233  in
                    let uu____2302 =
                      let uu____2303 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2303  in
                    FStar_Syntax_Util.abs uu____2302 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2319 = mk_lid "wp_close"  in
                    register env1 uu____2319 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2330 =
                      let uu____2331 =
                        let uu____2332 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2332
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2331  in
                    FStar_Pervasives_Native.Some uu____2330  in
                  let mk_forall1 x body =
                    let uu____2344 =
                      let uu____2351 =
                        let uu____2352 =
                          let uu____2369 =
                            let uu____2380 =
                              let uu____2389 =
                                let uu____2390 =
                                  let uu____2391 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2391]  in
                                FStar_Syntax_Util.abs uu____2390 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2389  in
                            [uu____2380]  in
                          (FStar_Syntax_Util.tforall, uu____2369)  in
                        FStar_Syntax_Syntax.Tm_app uu____2352  in
                      FStar_Syntax_Syntax.mk uu____2351  in
                    uu____2344 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2452 =
                      let uu____2453 = FStar_Syntax_Subst.compress t  in
                      uu____2453.FStar_Syntax_Syntax.n  in
                    match uu____2452 with
                    | FStar_Syntax_Syntax.Tm_type uu____2457 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2490  ->
                              match uu____2490 with
                              | (b,uu____2499) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2504 -> true  in
                  let rec is_monotonic t =
                    let uu____2517 =
                      let uu____2518 = FStar_Syntax_Subst.compress t  in
                      uu____2518.FStar_Syntax_Syntax.n  in
                    match uu____2517 with
                    | FStar_Syntax_Syntax.Tm_type uu____2522 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2555  ->
                              match uu____2555 with
                              | (b,uu____2564) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2569 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2643 =
                      let uu____2644 = FStar_Syntax_Subst.compress t1  in
                      uu____2644.FStar_Syntax_Syntax.n  in
                    match uu____2643 with
                    | FStar_Syntax_Syntax.Tm_type uu____2649 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2652);
                                      FStar_Syntax_Syntax.pos = uu____2653;
                                      FStar_Syntax_Syntax.vars = uu____2654;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2698 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2698
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2708 =
                              let uu____2711 =
                                let uu____2722 =
                                  let uu____2731 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2731  in
                                [uu____2722]  in
                              FStar_Syntax_Util.mk_app x uu____2711  in
                            let uu____2748 =
                              let uu____2751 =
                                let uu____2762 =
                                  let uu____2771 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2771  in
                                [uu____2762]  in
                              FStar_Syntax_Util.mk_app y uu____2751  in
                            mk_rel1 b uu____2708 uu____2748  in
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
                             let uu____2795 =
                               let uu____2798 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2801 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2798 uu____2801  in
                             let uu____2804 =
                               let uu____2807 =
                                 let uu____2810 =
                                   let uu____2821 =
                                     let uu____2830 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2830
                                      in
                                   [uu____2821]  in
                                 FStar_Syntax_Util.mk_app x uu____2810  in
                               let uu____2847 =
                                 let uu____2850 =
                                   let uu____2861 =
                                     let uu____2870 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2870
                                      in
                                   [uu____2861]  in
                                 FStar_Syntax_Util.mk_app y uu____2850  in
                               mk_rel1 b uu____2807 uu____2847  in
                             FStar_Syntax_Util.mk_imp uu____2795 uu____2804
                              in
                           let uu____2887 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2887)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2890);
                                      FStar_Syntax_Syntax.pos = uu____2891;
                                      FStar_Syntax_Syntax.vars = uu____2892;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2936 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2936
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2946 =
                              let uu____2949 =
                                let uu____2960 =
                                  let uu____2969 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2969  in
                                [uu____2960]  in
                              FStar_Syntax_Util.mk_app x uu____2949  in
                            let uu____2986 =
                              let uu____2989 =
                                let uu____3000 =
                                  let uu____3009 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____3009  in
                                [uu____3000]  in
                              FStar_Syntax_Util.mk_app y uu____2989  in
                            mk_rel1 b uu____2946 uu____2986  in
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
                             let uu____3033 =
                               let uu____3036 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____3039 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____3036 uu____3039  in
                             let uu____3042 =
                               let uu____3045 =
                                 let uu____3048 =
                                   let uu____3059 =
                                     let uu____3068 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____3068
                                      in
                                   [uu____3059]  in
                                 FStar_Syntax_Util.mk_app x uu____3048  in
                               let uu____3085 =
                                 let uu____3088 =
                                   let uu____3099 =
                                     let uu____3108 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____3108
                                      in
                                   [uu____3099]  in
                                 FStar_Syntax_Util.mk_app y uu____3088  in
                               mk_rel1 b uu____3045 uu____3085  in
                             FStar_Syntax_Util.mk_imp uu____3033 uu____3042
                              in
                           let uu____3125 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____3125)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___13_3164 = t1  in
                          let uu____3165 =
                            let uu____3166 =
                              let uu____3181 =
                                let uu____3184 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3184  in
                              ([binder], uu____3181)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____3166  in
                          {
                            FStar_Syntax_Syntax.n = uu____3165;
                            FStar_Syntax_Syntax.pos =
                              (uu___13_3164.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___13_3164.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3207 ->
                        failwith "unhandled arrow"
                    | uu____3225 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____3262 =
                        let uu____3263 = FStar_Syntax_Subst.compress t1  in
                        uu____3263.FStar_Syntax_Syntax.n  in
                      match uu____3262 with
                      | FStar_Syntax_Syntax.Tm_type uu____3266 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3293 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3293
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3314 =
                                let uu____3315 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3315 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3314
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3345 =
                            let uu____3356 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3374  ->
                                     match uu____3374 with
                                     | (t2,q) ->
                                         let uu____3394 = project i x  in
                                         let uu____3397 = project i y  in
                                         mk_stronger t2 uu____3394 uu____3397)
                                args
                               in
                            match uu____3356 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3345 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3451);
                                      FStar_Syntax_Syntax.pos = uu____3452;
                                      FStar_Syntax_Syntax.vars = uu____3453;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3497  ->
                                   match uu____3497 with
                                   | (bv,q) ->
                                       let uu____3511 =
                                         let uu____3513 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3513  in
                                       FStar_Syntax_Syntax.gen_bv uu____3511
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3522 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3522) bvs
                             in
                          let body =
                            let uu____3524 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3527 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3524 uu____3527  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3536);
                                      FStar_Syntax_Syntax.pos = uu____3537;
                                      FStar_Syntax_Syntax.vars = uu____3538;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3582  ->
                                   match uu____3582 with
                                   | (bv,q) ->
                                       let uu____3596 =
                                         let uu____3598 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____3598  in
                                       FStar_Syntax_Syntax.gen_bv uu____3596
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3607 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3607) bvs
                             in
                          let body =
                            let uu____3609 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3612 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3609 uu____3612  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3619 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3622 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3625 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3628 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3622 uu____3625 uu____3628  in
                    let uu____3631 =
                      let uu____3632 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3632  in
                    FStar_Syntax_Util.abs uu____3631 body ret_tot_type  in
                  let stronger1 =
                    let uu____3674 = mk_lid "stronger"  in
                    register env1 uu____3674 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3682 = FStar_Util.prefix gamma  in
                    match uu____3682 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3748 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3748
                             in
                          let uu____3753 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3753 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3763 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3763  in
                              let guard_free1 =
                                let uu____3775 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3775  in
                              let pat =
                                let uu____3779 =
                                  let uu____3790 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3790]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3779
                                 in
                              let pattern_guarded_body =
                                let uu____3818 =
                                  let uu____3819 =
                                    let uu____3826 =
                                      let uu____3827 =
                                        let uu____3840 =
                                          let uu____3851 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3851]  in
                                        [uu____3840]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3827
                                       in
                                    (body, uu____3826)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3819  in
                                mk1 uu____3818  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3898 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3907 =
                            let uu____3910 =
                              let uu____3911 =
                                let uu____3914 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3917 =
                                  let uu____3928 = args_of_binders1 wp_args
                                     in
                                  let uu____3931 =
                                    let uu____3934 =
                                      let uu____3935 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3935
                                       in
                                    [uu____3934]  in
                                  FStar_List.append uu____3928 uu____3931  in
                                FStar_Syntax_Util.mk_app uu____3914
                                  uu____3917
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3911  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3910
                             in
                          FStar_Syntax_Util.abs gamma uu____3907
                            ret_gtot_type
                           in
                        let uu____3936 =
                          let uu____3937 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3937  in
                        FStar_Syntax_Util.abs uu____3936 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____3953 = mk_lid "ite_wp"  in
                    register env1 uu____3953 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3961 = FStar_Util.prefix gamma  in
                    match uu____3961 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____4019 =
                            let uu____4020 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____4027 =
                              let uu____4038 =
                                let uu____4047 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____4047  in
                              [uu____4038]  in
                            FStar_Syntax_Util.mk_app uu____4020 uu____4027
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____4019
                           in
                        let uu____4064 =
                          let uu____4065 =
                            let uu____4074 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____4074 gamma  in
                          FStar_List.append binders uu____4065  in
                        FStar_Syntax_Util.abs uu____4064 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____4096 = mk_lid "null_wp"  in
                    register env1 uu____4096 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____4109 =
                        let uu____4120 =
                          let uu____4123 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____4124 =
                            let uu____4127 =
                              let uu____4128 =
                                let uu____4139 =
                                  let uu____4148 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____4148  in
                                [uu____4139]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____4128
                               in
                            let uu____4165 =
                              let uu____4168 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____4168]  in
                            uu____4127 :: uu____4165  in
                          uu____4123 :: uu____4124  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4120
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____4109  in
                    let uu____4177 =
                      let uu____4178 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____4178  in
                    FStar_Syntax_Util.abs uu____4177 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____4194 = mk_lid "wp_trivial"  in
                    register env1 uu____4194 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____4200 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____4200
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4212 =
                      let uu____4213 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4213  in
                    let uu____4261 =
                      let uu___14_4262 = ed  in
                      let uu____4263 =
                        let uu____4264 = c wp_if_then_else2  in
                        ([], uu____4264)  in
                      let uu____4271 =
                        let uu____4272 = c ite_wp2  in ([], uu____4272)  in
                      let uu____4279 =
                        let uu____4280 = c stronger2  in ([], uu____4280)  in
                      let uu____4287 =
                        let uu____4288 = c wp_close2  in ([], uu____4288)  in
                      let uu____4295 =
                        let uu____4296 = c wp_assert2  in ([], uu____4296)
                         in
                      let uu____4303 =
                        let uu____4304 = c wp_assume2  in ([], uu____4304)
                         in
                      let uu____4311 =
                        let uu____4312 = c null_wp2  in ([], uu____4312)  in
                      let uu____4319 =
                        let uu____4320 = c wp_trivial2  in ([], uu____4320)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___14_4262.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___14_4262.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___14_4262.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___14_4262.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___14_4262.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___14_4262.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___14_4262.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____4263;
                        FStar_Syntax_Syntax.ite_wp = uu____4271;
                        FStar_Syntax_Syntax.stronger = uu____4279;
                        FStar_Syntax_Syntax.close_wp = uu____4287;
                        FStar_Syntax_Syntax.assert_p = uu____4295;
                        FStar_Syntax_Syntax.assume_p = uu____4303;
                        FStar_Syntax_Syntax.null_wp = uu____4311;
                        FStar_Syntax_Syntax.trivial = uu____4319;
                        FStar_Syntax_Syntax.repr =
                          (uu___14_4262.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___14_4262.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___14_4262.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___14_4262.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___14_4262.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4212, uu____4261)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___15_4344 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___15_4344.subst);
        tc_const = (uu___15_4344.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4365 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4385 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____4406) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___1_4420  ->
                match uu___1_4420 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4423 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____4425 ->
        let uu____4426 =
          let uu____4432 =
            let uu____4434 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____4434
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____4432)  in
        FStar_Errors.raise_error uu____4426 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___2_4444  ->
    match uu___2_4444 with
    | N t ->
        let uu____4447 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4447
    | M t ->
        let uu____4451 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4451
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____4460,c) -> nm_of_comp c
    | uu____4482 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4495 = nm_of_comp c  in
    match uu____4495 with | M uu____4497 -> true | N uu____4499 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4510 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4526 =
        let uu____4535 =
          let uu____4542 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4542  in
        [uu____4535]  in
      let uu____4561 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4526 uu____4561  in
    let uu____4564 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4564
  
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
        let uu____4606 =
          let uu____4607 =
            let uu____4622 =
              let uu____4631 =
                let uu____4638 =
                  let uu____4639 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4639  in
                let uu____4640 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4638, uu____4640)  in
              [uu____4631]  in
            let uu____4658 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4622, uu____4658)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4607  in
        mk1 uu____4606

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4698) ->
          let binders1 =
            FStar_List.map
              (fun uu____4744  ->
                 match uu____4744 with
                 | (bv,aqual) ->
                     let uu____4763 =
                       let uu___16_4764 = bv  in
                       let uu____4765 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___16_4764.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___16_4764.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4765
                       }  in
                     (uu____4763, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4770,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4772);
                             FStar_Syntax_Syntax.pos = uu____4773;
                             FStar_Syntax_Syntax.vars = uu____4774;_})
               ->
               let uu____4803 =
                 let uu____4804 =
                   let uu____4819 =
                     let uu____4822 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4822  in
                   (binders1, uu____4819)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4804  in
               mk1 uu____4803
           | uu____4833 ->
               let uu____4834 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4834 with
                | N hn ->
                    let uu____4836 =
                      let uu____4837 =
                        let uu____4852 =
                          let uu____4855 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4855  in
                        (binders1, uu____4852)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4837  in
                    mk1 uu____4836
                | M a ->
                    let uu____4867 =
                      let uu____4868 =
                        let uu____4883 =
                          let uu____4892 =
                            let uu____4901 =
                              let uu____4908 =
                                let uu____4909 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4909  in
                              let uu____4910 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4908, uu____4910)  in
                            [uu____4901]  in
                          FStar_List.append binders1 uu____4892  in
                        let uu____4934 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4883, uu____4934)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4868  in
                    mk1 uu____4867))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____5028 = f x  in
                    FStar_Util.string_builder_append strb uu____5028);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____5037 = f x1  in
                         FStar_Util.string_builder_append strb uu____5037))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____5041 =
              let uu____5047 =
                let uu____5049 = FStar_Syntax_Print.term_to_string t2  in
                let uu____5051 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____5049 uu____5051
                 in
              (FStar_Errors.Warning_DependencyFound, uu____5047)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____5041  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____5073 =
              let uu____5074 = FStar_Syntax_Subst.compress ty  in
              uu____5074.FStar_Syntax_Syntax.n  in
            match uu____5073 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5100 =
                  let uu____5102 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____5102  in
                if uu____5100
                then false
                else
                  (try
                     (fun uu___18_5119  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____5143 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____5143 s  in
                              let uu____5146 =
                                let uu____5148 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____5148  in
                              if uu____5146
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____5154 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____5154 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____5179  ->
                                          match uu____5179 with
                                          | (bv,uu____5191) ->
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
            | uu____5219 ->
                ((let uu____5221 =
                    let uu____5227 =
                      let uu____5229 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____5229
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____5227)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____5221);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____5245 =
              let uu____5246 = FStar_Syntax_Subst.compress head2  in
              uu____5246.FStar_Syntax_Syntax.n  in
            match uu____5245 with
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
                  (let uu____5252 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____5252)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____5255 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____5255 with
                 | ((uu____5265,ty),uu____5267) ->
                     let uu____5272 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____5272
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____5285 =
                         let uu____5286 = FStar_Syntax_Subst.compress res  in
                         uu____5286.FStar_Syntax_Syntax.n  in
                       (match uu____5285 with
                        | FStar_Syntax_Syntax.Tm_app uu____5290 -> true
                        | uu____5308 ->
                            ((let uu____5310 =
                                let uu____5316 =
                                  let uu____5318 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5318
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5316)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5310);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5326 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5328 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5331) ->
                is_valid_application t2
            | uu____5336 -> false  in
          let uu____5338 = is_valid_application head1  in
          if uu____5338
          then
            let uu____5341 =
              let uu____5342 =
                let uu____5359 =
                  FStar_List.map
                    (fun uu____5388  ->
                       match uu____5388 with
                       | (t2,qual) ->
                           let uu____5413 = star_type' env t2  in
                           (uu____5413, qual)) args
                   in
                (head1, uu____5359)  in
              FStar_Syntax_Syntax.Tm_app uu____5342  in
            mk1 uu____5341
          else
            (let uu____5430 =
               let uu____5436 =
                 let uu____5438 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5438
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5436)  in
             FStar_Errors.raise_err uu____5430)
      | FStar_Syntax_Syntax.Tm_bvar uu____5442 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5443 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5444 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5445 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5473 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5473 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___19_5481 = env  in
                 let uu____5482 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____5482;
                   subst = (uu___19_5481.subst);
                   tc_const = (uu___19_5481.tc_const)
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
               ((let uu___20_5509 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___20_5509.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___20_5509.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5516 =
            let uu____5517 =
              let uu____5524 = star_type' env t2  in (uu____5524, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5517  in
          mk1 uu____5516
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5576 =
            let uu____5577 =
              let uu____5604 = star_type' env e  in
              let uu____5607 =
                let uu____5624 =
                  let uu____5633 = star_type' env t2  in
                  FStar_Util.Inl uu____5633  in
                (uu____5624, FStar_Pervasives_Native.None)  in
              (uu____5604, uu____5607, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5577  in
          mk1 uu____5576
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5721 =
            let uu____5722 =
              let uu____5749 = star_type' env e  in
              let uu____5752 =
                let uu____5769 =
                  let uu____5778 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5778  in
                (uu____5769, FStar_Pervasives_Native.None)  in
              (uu____5749, uu____5752, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5722  in
          mk1 uu____5721
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5819,(uu____5820,FStar_Pervasives_Native.Some uu____5821),uu____5822)
          ->
          let uu____5871 =
            let uu____5877 =
              let uu____5879 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5879
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5877)  in
          FStar_Errors.raise_err uu____5871
      | FStar_Syntax_Syntax.Tm_refine uu____5883 ->
          let uu____5890 =
            let uu____5896 =
              let uu____5898 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5898
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5896)  in
          FStar_Errors.raise_err uu____5890
      | FStar_Syntax_Syntax.Tm_uinst uu____5902 ->
          let uu____5909 =
            let uu____5915 =
              let uu____5917 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5917
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5915)  in
          FStar_Errors.raise_err uu____5909
      | FStar_Syntax_Syntax.Tm_quoted uu____5921 ->
          let uu____5928 =
            let uu____5934 =
              let uu____5936 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5936
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5934)  in
          FStar_Errors.raise_err uu____5928
      | FStar_Syntax_Syntax.Tm_constant uu____5940 ->
          let uu____5941 =
            let uu____5947 =
              let uu____5949 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5949
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5947)  in
          FStar_Errors.raise_err uu____5941
      | FStar_Syntax_Syntax.Tm_match uu____5953 ->
          let uu____5976 =
            let uu____5982 =
              let uu____5984 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5984
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5982)  in
          FStar_Errors.raise_err uu____5976
      | FStar_Syntax_Syntax.Tm_let uu____5988 ->
          let uu____6002 =
            let uu____6008 =
              let uu____6010 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____6010
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6008)  in
          FStar_Errors.raise_err uu____6002
      | FStar_Syntax_Syntax.Tm_uvar uu____6014 ->
          let uu____6027 =
            let uu____6033 =
              let uu____6035 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____6035
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6033)  in
          FStar_Errors.raise_err uu____6027
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6039 =
            let uu____6045 =
              let uu____6047 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____6047
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____6045)  in
          FStar_Errors.raise_err uu____6039
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6052 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____6052
      | FStar_Syntax_Syntax.Tm_delayed uu____6055 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___4_6087  ->
    match uu___4_6087 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___3_6098  ->
                match uu___3_6098 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____6101 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____6111 =
      let uu____6112 = FStar_Syntax_Subst.compress t  in
      uu____6112.FStar_Syntax_Syntax.n  in
    match uu____6111 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____6144 =
            let uu____6145 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____6145  in
          is_C uu____6144  in
        if r
        then
          ((let uu____6169 =
              let uu____6171 =
                FStar_List.for_all
                  (fun uu____6182  ->
                     match uu____6182 with | (h,uu____6191) -> is_C h) args
                 in
              Prims.op_Negation uu____6171  in
            if uu____6169 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____6204 =
              let uu____6206 =
                FStar_List.for_all
                  (fun uu____6218  ->
                     match uu____6218 with
                     | (h,uu____6227) ->
                         let uu____6232 = is_C h  in
                         Prims.op_Negation uu____6232) args
                 in
              Prims.op_Negation uu____6206  in
            if uu____6204 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____6261 = nm_of_comp comp  in
        (match uu____6261 with
         | M t1 ->
             ((let uu____6265 = is_C t1  in
               if uu____6265 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____6274) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6280) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____6286,uu____6287) -> is_C t1
    | uu____6328 -> false
  
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
          let uu____6364 =
            let uu____6365 =
              let uu____6382 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____6385 =
                let uu____6396 =
                  let uu____6405 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____6405)  in
                [uu____6396]  in
              (uu____6382, uu____6385)  in
            FStar_Syntax_Syntax.Tm_app uu____6365  in
          mk1 uu____6364  in
        let uu____6441 =
          let uu____6442 = FStar_Syntax_Syntax.mk_binder p  in [uu____6442]
           in
        FStar_Syntax_Util.abs uu____6441 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___5_6467  ->
    match uu___5_6467 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6470 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6708 =
          match uu____6708 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6745 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6748 =
                       let uu____6750 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6750  in
                     Prims.op_Negation uu____6748)
                   in
                if uu____6745
                then
                  let uu____6752 =
                    let uu____6758 =
                      let uu____6760 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6762 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6764 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6760 uu____6762 uu____6764
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6758)  in
                  FStar_Errors.raise_err uu____6752
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6789 = mk_return env t1 s_e  in
                     ((M t1), uu____6789, u_e)))
               | (M t1,N t2) ->
                   let uu____6796 =
                     let uu____6802 =
                       let uu____6804 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6806 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6808 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6804 uu____6806 uu____6808
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6802)
                      in
                   FStar_Errors.raise_err uu____6796)
           in
        let ensure_m env1 e2 =
          let strip_m uu___6_6860 =
            match uu___6_6860 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6876 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6897 =
                let uu____6903 =
                  let uu____6905 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6905
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6903)  in
              FStar_Errors.raise_error uu____6897 e2.FStar_Syntax_Syntax.pos
          | M uu____6915 ->
              let uu____6916 = check env1 e2 context_nm  in
              strip_m uu____6916
           in
        let uu____6923 =
          let uu____6924 = FStar_Syntax_Subst.compress e  in
          uu____6924.FStar_Syntax_Syntax.n  in
        match uu____6923 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6933 ->
            let uu____6934 = infer env e  in return_if uu____6934
        | FStar_Syntax_Syntax.Tm_name uu____6941 ->
            let uu____6942 = infer env e  in return_if uu____6942
        | FStar_Syntax_Syntax.Tm_fvar uu____6949 ->
            let uu____6950 = infer env e  in return_if uu____6950
        | FStar_Syntax_Syntax.Tm_abs uu____6957 ->
            let uu____6976 = infer env e  in return_if uu____6976
        | FStar_Syntax_Syntax.Tm_constant uu____6983 ->
            let uu____6984 = infer env e  in return_if uu____6984
        | FStar_Syntax_Syntax.Tm_quoted uu____6991 ->
            let uu____6998 = infer env e  in return_if uu____6998
        | FStar_Syntax_Syntax.Tm_app uu____7005 ->
            let uu____7022 = infer env e  in return_if uu____7022
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____7030 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____7030 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____7095) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7101) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7107,uu____7108) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____7149 ->
            let uu____7163 =
              let uu____7165 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____7165  in
            failwith uu____7163
        | FStar_Syntax_Syntax.Tm_type uu____7174 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____7182 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____7204 ->
            let uu____7211 =
              let uu____7213 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____7213  in
            failwith uu____7211
        | FStar_Syntax_Syntax.Tm_uvar uu____7222 ->
            let uu____7235 =
              let uu____7237 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____7237  in
            failwith uu____7235
        | FStar_Syntax_Syntax.Tm_delayed uu____7246 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____7276 =
              let uu____7278 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____7278  in
            failwith uu____7276

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
      let uu____7308 =
        let uu____7309 = FStar_Syntax_Subst.compress e  in
        uu____7309.FStar_Syntax_Syntax.n  in
      match uu____7308 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7328 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____7328
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____7379;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____7380;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____7386 =
                  let uu___21_7387 = rc  in
                  let uu____7388 =
                    let uu____7393 =
                      let uu____7396 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____7396  in
                    FStar_Pervasives_Native.Some uu____7393  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___21_7387.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____7388;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___21_7387.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____7386
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___22_7408 = env  in
            let uu____7409 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____7409;
              subst = (uu___22_7408.subst);
              tc_const = (uu___22_7408.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____7435  ->
                 match uu____7435 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___23_7458 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___23_7458.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___23_7458.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____7459 =
            FStar_List.fold_left
              (fun uu____7490  ->
                 fun uu____7491  ->
                   match (uu____7490, uu____7491) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7549 = is_C c  in
                       if uu____7549
                       then
                         let xw =
                           let uu____7559 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7559
                            in
                         let x =
                           let uu___24_7562 = bv  in
                           let uu____7563 =
                             let uu____7566 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7566  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___24_7562.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___24_7562.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7563
                           }  in
                         let env3 =
                           let uu___25_7568 = env2  in
                           let uu____7569 =
                             let uu____7572 =
                               let uu____7573 =
                                 let uu____7580 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7580)  in
                               FStar_Syntax_Syntax.NT uu____7573  in
                             uu____7572 :: (env2.subst)  in
                           {
                             tcenv = (uu___25_7568.tcenv);
                             subst = uu____7569;
                             tc_const = (uu___25_7568.tc_const)
                           }  in
                         let uu____7585 =
                           let uu____7588 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7589 =
                             let uu____7592 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7592 :: acc  in
                           uu____7588 :: uu____7589  in
                         (env3, uu____7585)
                       else
                         (let x =
                            let uu___26_7598 = bv  in
                            let uu____7599 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___26_7598.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___26_7598.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7599
                            }  in
                          let uu____7602 =
                            let uu____7605 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7605 :: acc  in
                          (env2, uu____7602))) (env1, []) binders1
             in
          (match uu____7459 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7625 =
                 let check_what =
                   let uu____7651 = is_monadic rc_opt1  in
                   if uu____7651 then check_m else check_n  in
                 let uu____7668 = check_what env2 body1  in
                 match uu____7668 with
                 | (t,s_body,u_body) ->
                     let uu____7688 =
                       let uu____7691 =
                         let uu____7692 = is_monadic rc_opt1  in
                         if uu____7692 then M t else N t  in
                       comp_of_nm uu____7691  in
                     (uu____7688, s_body, u_body)
                  in
               (match uu____7625 with
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
                                 let uu____7732 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___7_7738  ->
                                           match uu___7_7738 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7741 -> false))
                                    in
                                 if uu____7732
                                 then
                                   let uu____7744 =
                                     FStar_List.filter
                                       (fun uu___8_7748  ->
                                          match uu___8_7748 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7751 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7744
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7762 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___9_7768  ->
                                         match uu___9_7768 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7771 -> false))
                                  in
                               if uu____7762
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___10_7780  ->
                                        match uu___10_7780 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7783 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7785 =
                                   let uu____7786 =
                                     let uu____7791 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7791
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7786 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____7785
                               else
                                 (let uu____7798 =
                                    let uu___27_7799 = rc  in
                                    let uu____7800 =
                                      let uu____7805 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7805
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___27_7799.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7800;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___27_7799.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7798))
                       in
                    let uu____7810 =
                      let comp1 =
                        let uu____7818 = is_monadic rc_opt1  in
                        let uu____7820 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7818 uu____7820
                         in
                      let uu____7821 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7821,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7810 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7859 =
                             let uu____7860 =
                               let uu____7879 =
                                 let uu____7882 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7882 s_rc_opt  in
                               (s_binders1, s_body1, uu____7879)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7860  in
                           mk1 uu____7859  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7902 =
                             let uu____7903 =
                               let uu____7922 =
                                 let uu____7925 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7925 u_rc_opt  in
                               (u_binders2, u_body2, uu____7922)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7903  in
                           mk1 uu____7902  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7941;_};
            FStar_Syntax_Syntax.fv_delta = uu____7942;
            FStar_Syntax_Syntax.fv_qual = uu____7943;_}
          ->
          let uu____7946 =
            let uu____7951 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7951  in
          (match uu____7946 with
           | (uu____7982,t) ->
               let uu____7984 =
                 let uu____7985 = normalize1 t  in N uu____7985  in
               (uu____7984, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7986;
             FStar_Syntax_Syntax.vars = uu____7987;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8066 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8066 with
           | (unary_op1,uu____8090) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8161;
             FStar_Syntax_Syntax.vars = uu____8162;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____8258 = FStar_Syntax_Util.head_and_args e  in
          (match uu____8258 with
           | (unary_op1,uu____8282) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8361;
             FStar_Syntax_Syntax.vars = uu____8362;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____8400 = infer env a  in
          (match uu____8400 with
           | (t,s,u) ->
               let uu____8416 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8416 with
                | (head1,uu____8440) ->
                    let uu____8465 =
                      let uu____8466 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____8466  in
                    let uu____8467 =
                      let uu____8468 =
                        let uu____8469 =
                          let uu____8486 =
                            let uu____8497 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8497]  in
                          (head1, uu____8486)  in
                        FStar_Syntax_Syntax.Tm_app uu____8469  in
                      mk1 uu____8468  in
                    let uu____8534 =
                      let uu____8535 =
                        let uu____8536 =
                          let uu____8553 =
                            let uu____8564 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8564]  in
                          (head1, uu____8553)  in
                        FStar_Syntax_Syntax.Tm_app uu____8536  in
                      mk1 uu____8535  in
                    (uu____8465, uu____8467, uu____8534)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8601;
             FStar_Syntax_Syntax.vars = uu____8602;_},(a1,uu____8604)::a2::[])
          ->
          let uu____8660 = infer env a1  in
          (match uu____8660 with
           | (t,s,u) ->
               let uu____8676 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8676 with
                | (head1,uu____8700) ->
                    let uu____8725 =
                      let uu____8726 =
                        let uu____8727 =
                          let uu____8744 =
                            let uu____8755 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8755; a2]  in
                          (head1, uu____8744)  in
                        FStar_Syntax_Syntax.Tm_app uu____8727  in
                      mk1 uu____8726  in
                    let uu____8800 =
                      let uu____8801 =
                        let uu____8802 =
                          let uu____8819 =
                            let uu____8830 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8830; a2]  in
                          (head1, uu____8819)  in
                        FStar_Syntax_Syntax.Tm_app uu____8802  in
                      mk1 uu____8801  in
                    (t, uu____8725, uu____8800)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8875;
             FStar_Syntax_Syntax.vars = uu____8876;_},uu____8877)
          ->
          let uu____8902 =
            let uu____8908 =
              let uu____8910 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8910
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8908)  in
          FStar_Errors.raise_error uu____8902 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8920;
             FStar_Syntax_Syntax.vars = uu____8921;_},uu____8922)
          ->
          let uu____8947 =
            let uu____8953 =
              let uu____8955 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8955
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8953)  in
          FStar_Errors.raise_error uu____8947 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8991 = check_n env head1  in
          (match uu____8991 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____9014 =
                   let uu____9015 = FStar_Syntax_Subst.compress t  in
                   uu____9015.FStar_Syntax_Syntax.n  in
                 match uu____9014 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____9019 -> true
                 | uu____9035 -> false  in
               let rec flatten1 t =
                 let uu____9057 =
                   let uu____9058 = FStar_Syntax_Subst.compress t  in
                   uu____9058.FStar_Syntax_Syntax.n  in
                 match uu____9057 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____9077);
                                FStar_Syntax_Syntax.pos = uu____9078;
                                FStar_Syntax_Syntax.vars = uu____9079;_})
                     when is_arrow t1 ->
                     let uu____9108 = flatten1 t1  in
                     (match uu____9108 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9208,uu____9209)
                     -> flatten1 e1
                 | uu____9250 ->
                     let uu____9251 =
                       let uu____9257 =
                         let uu____9259 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____9259
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____9257)  in
                     FStar_Errors.raise_err uu____9251
                  in
               let uu____9277 = flatten1 t_head  in
               (match uu____9277 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____9352 =
                          let uu____9358 =
                            let uu____9360 = FStar_Util.string_of_int n1  in
                            let uu____9368 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____9380 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____9360 uu____9368 uu____9380
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____9358)
                           in
                        FStar_Errors.raise_err uu____9352)
                     else ();
                     (let uu____9392 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____9392 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____9445 args1 =
                            match uu____9445 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9545 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____9545
                                 | (binders3,[]) ->
                                     let uu____9583 =
                                       let uu____9584 =
                                         let uu____9587 =
                                           let uu____9588 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9588
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9587
                                          in
                                       uu____9584.FStar_Syntax_Syntax.n  in
                                     (match uu____9583 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9621 =
                                            let uu____9622 =
                                              let uu____9623 =
                                                let uu____9638 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9638)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9623
                                               in
                                            mk1 uu____9622  in
                                          N uu____9621
                                      | uu____9651 -> failwith "wat?")
                                 | ([],uu____9653::uu____9654) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9707)::binders3,(arg,uu____9710)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9797 = FStar_List.splitAt n' binders1  in
                          (match uu____9797 with
                           | (binders2,uu____9835) ->
                               let uu____9868 =
                                 let uu____9891 =
                                   FStar_List.map2
                                     (fun uu____9953  ->
                                        fun uu____9954  ->
                                          match (uu____9953, uu____9954) with
                                          | ((bv,uu____10002),(arg,q)) ->
                                              let uu____10031 =
                                                let uu____10032 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____10032.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____10031 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____10053 ->
                                                   let uu____10054 =
                                                     let uu____10061 =
                                                       star_type' env arg  in
                                                     (uu____10061, q)  in
                                                   (uu____10054, [(arg, q)])
                                               | uu____10098 ->
                                                   let uu____10099 =
                                                     check_n env arg  in
                                                   (match uu____10099 with
                                                    | (uu____10124,s_arg,u_arg)
                                                        ->
                                                        let uu____10127 =
                                                          let uu____10136 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____10136
                                                          then
                                                            let uu____10147 =
                                                              let uu____10154
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____10154,
                                                                q)
                                                               in
                                                            [uu____10147;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____10127))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9891  in
                               (match uu____9868 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____10282 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____10295 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____10282, uu____10295)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____10364) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____10370) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____10376,uu____10377) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10419 =
            let uu____10420 = env.tc_const c  in N uu____10420  in
          (uu____10419, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____10427 ->
          let uu____10441 =
            let uu____10443 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____10443  in
          failwith uu____10441
      | FStar_Syntax_Syntax.Tm_type uu____10452 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____10460 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____10482 ->
          let uu____10489 =
            let uu____10491 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____10491  in
          failwith uu____10489
      | FStar_Syntax_Syntax.Tm_uvar uu____10500 ->
          let uu____10513 =
            let uu____10515 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____10515  in
          failwith uu____10513
      | FStar_Syntax_Syntax.Tm_delayed uu____10524 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10554 =
            let uu____10556 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10556  in
          failwith uu____10554

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
          let uu____10605 = check_n env e0  in
          match uu____10605 with
          | (uu____10618,s_e0,u_e0) ->
              let uu____10621 =
                let uu____10650 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10711 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10711 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___28_10753 = env  in
                             let uu____10754 =
                               let uu____10755 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____10755
                                in
                             {
                               tcenv = uu____10754;
                               subst = (uu___28_10753.subst);
                               tc_const = (uu___28_10753.tc_const)
                             }  in
                           let uu____10758 = f env1 body  in
                           (match uu____10758 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10830 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10650  in
              (match uu____10621 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10936 = FStar_List.hd nms  in
                     match uu____10936 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___11_10945  ->
                          match uu___11_10945 with
                          | M uu____10947 -> true
                          | uu____10949 -> false) nms
                      in
                   let uu____10951 =
                     let uu____10988 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____11078  ->
                              match uu____11078 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____11262 =
                                         check env original_body (M t2)  in
                                       (match uu____11262 with
                                        | (uu____11299,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____11338,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10988  in
                   (match uu____10951 with
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
                              (fun uu____11527  ->
                                 match uu____11527 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11578 =
                                         let uu____11579 =
                                           let uu____11596 =
                                             let uu____11607 =
                                               let uu____11616 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11619 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11616, uu____11619)  in
                                             [uu____11607]  in
                                           (s_body, uu____11596)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11579
                                          in
                                       mk1 uu____11578  in
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
                            let uu____11754 =
                              let uu____11755 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11755]  in
                            let uu____11774 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11754 uu____11774
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11798 =
                              let uu____11807 =
                                let uu____11814 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11814
                                 in
                              [uu____11807]  in
                            let uu____11833 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11798 uu____11833
                             in
                          let uu____11836 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11875 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11836, uu____11875)
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
                           let uu____11985 =
                             let uu____11986 =
                               let uu____11987 =
                                 let uu____12014 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____12014,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11987
                                in
                             mk1 uu____11986  in
                           let uu____12073 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11985, uu____12073))))

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
              let uu____12138 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____12138]  in
            let uu____12157 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____12157 with
            | (x_binders1,e21) ->
                let uu____12170 = infer env e1  in
                (match uu____12170 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____12187 = is_C t1  in
                       if uu____12187
                       then
                         let uu___29_12190 = binding  in
                         let uu____12191 =
                           let uu____12194 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____12194  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___29_12190.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___29_12190.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____12191;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___29_12190.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___29_12190.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___29_12190.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___29_12190.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___30_12198 = env  in
                       let uu____12199 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___31_12201 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___31_12201.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___31_12201.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12199;
                         subst = (uu___30_12198.subst);
                         tc_const = (uu___30_12198.tc_const)
                       }  in
                     let uu____12202 = proceed env1 e21  in
                     (match uu____12202 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___32_12219 = binding  in
                            let uu____12220 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___32_12219.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___32_12219.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____12220;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___32_12219.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___32_12219.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___32_12219.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___32_12219.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____12223 =
                            let uu____12224 =
                              let uu____12225 =
                                let uu____12239 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___33_12256 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___33_12256.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___33_12256.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___33_12256.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___33_12256.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___33_12256.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___33_12256.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12239)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12225  in
                            mk1 uu____12224  in
                          let uu____12257 =
                            let uu____12258 =
                              let uu____12259 =
                                let uu____12273 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___34_12290 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___34_12290.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___34_12290.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___34_12290.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___34_12290.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___34_12290.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___34_12290.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12273)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12259  in
                            mk1 uu____12258  in
                          (nm_rec, uu____12223, uu____12257))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___35_12295 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___35_12295.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___35_12295.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___35_12295.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___35_12295.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___35_12295.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___36_12297 = env  in
                       let uu____12298 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___37_12300 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___37_12300.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___37_12300.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____12298;
                         subst = (uu___36_12297.subst);
                         tc_const = (uu___36_12297.tc_const)
                       }  in
                     let uu____12301 = ensure_m env1 e21  in
                     (match uu____12301 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____12325 =
                              let uu____12326 =
                                let uu____12343 =
                                  let uu____12354 =
                                    let uu____12363 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____12366 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12363, uu____12366)  in
                                  [uu____12354]  in
                                (s_e2, uu____12343)  in
                              FStar_Syntax_Syntax.Tm_app uu____12326  in
                            mk1 uu____12325  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____12408 =
                              let uu____12409 =
                                let uu____12426 =
                                  let uu____12437 =
                                    let uu____12446 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____12446)  in
                                  [uu____12437]  in
                                (s_e1, uu____12426)  in
                              FStar_Syntax_Syntax.Tm_app uu____12409  in
                            mk1 uu____12408  in
                          let uu____12482 =
                            let uu____12483 =
                              let uu____12484 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____12484]  in
                            FStar_Syntax_Util.abs uu____12483 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____12503 =
                            let uu____12504 =
                              let uu____12505 =
                                let uu____12519 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___38_12536 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___38_12536.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___38_12536.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___38_12536.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___38_12536.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___38_12536.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___38_12536.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____12519)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____12505  in
                            mk1 uu____12504  in
                          ((M t2), uu____12482, uu____12503)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12546 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____12546  in
      let uu____12547 = check env e mn  in
      match uu____12547 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12563 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____12586 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____12586  in
      let uu____12587 = check env e mn  in
      match uu____12587 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12603 -> failwith "[check_m]: impossible"

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
        (let uu____12636 =
           let uu____12638 = is_C c  in Prims.op_Negation uu____12638  in
         if uu____12636 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12652 =
           let uu____12653 = FStar_Syntax_Subst.compress c  in
           uu____12653.FStar_Syntax_Syntax.n  in
         match uu____12652 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12682 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12682 with
              | (wp_head,wp_args) ->
                  ((let uu____12726 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12745 =
                           let uu____12747 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12747
                            in
                         Prims.op_Negation uu____12745)
                       in
                    if uu____12726 then failwith "mismatch" else ());
                   (let uu____12760 =
                      let uu____12761 =
                        let uu____12778 =
                          FStar_List.map2
                            (fun uu____12816  ->
                               fun uu____12817  ->
                                 match (uu____12816, uu____12817) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12879 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12879
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12888 =
                                         let uu____12890 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12890 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12888
                                       then
                                         let uu____12892 =
                                           let uu____12898 =
                                             let uu____12900 =
                                               print_implicit q  in
                                             let uu____12902 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12900 uu____12902
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12898)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12892
                                       else ());
                                      (let uu____12908 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12908, q)))) args wp_args
                           in
                        (head1, uu____12778)  in
                      FStar_Syntax_Syntax.Tm_app uu____12761  in
                    mk1 uu____12760)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12954 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12954 with
              | (binders_orig,comp1) ->
                  let uu____12961 =
                    let uu____12978 =
                      FStar_List.map
                        (fun uu____13018  ->
                           match uu____13018 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____13046 = is_C h  in
                               if uu____13046
                               then
                                 let w' =
                                   let uu____13062 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____13062
                                    in
                                 let uu____13064 =
                                   let uu____13073 =
                                     let uu____13082 =
                                       let uu____13089 =
                                         let uu____13090 =
                                           let uu____13091 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____13091  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____13090
                                          in
                                       (uu____13089, q)  in
                                     [uu____13082]  in
                                   (w', q) :: uu____13073  in
                                 (w', uu____13064)
                               else
                                 (let x =
                                    let uu____13125 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____13125
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12978  in
                  (match uu____12961 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____13199 =
                           let uu____13202 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____13202
                            in
                         FStar_Syntax_Subst.subst_comp uu____13199 comp1  in
                       let app =
                         let uu____13206 =
                           let uu____13207 =
                             let uu____13224 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____13243 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____13244 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____13243, uu____13244)) bvs
                                in
                             (wp, uu____13224)  in
                           FStar_Syntax_Syntax.Tm_app uu____13207  in
                         mk1 uu____13206  in
                       let comp3 =
                         let uu____13259 = type_of_comp comp2  in
                         let uu____13260 = is_monadic_comp comp2  in
                         trans_G env uu____13259 uu____13260 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____13263,uu____13264) ->
             trans_F_ env e wp
         | uu____13305 -> failwith "impossible trans_F_")

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
            let uu____13313 =
              let uu____13314 = star_type' env h  in
              let uu____13317 =
                let uu____13328 =
                  let uu____13337 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____13337)  in
                [uu____13328]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____13314;
                FStar_Syntax_Syntax.effect_args = uu____13317;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____13313
          else
            (let uu____13363 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____13363)

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
    fun t  -> let uu____13384 = n env.tcenv t  in star_type' env uu____13384
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____13404 = n env.tcenv t  in check_n env uu____13404
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____13421 = n env.tcenv c  in
        let uu____13422 = n env.tcenv wp  in
        trans_F_ env uu____13421 uu____13422
  