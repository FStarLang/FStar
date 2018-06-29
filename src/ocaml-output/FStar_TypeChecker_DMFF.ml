open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__env : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts,FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___348_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___348_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___348_123.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____124
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____134 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____134
             then
               (d "Elaborating extra WP combinators";
                (let uu____136 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____136))
             else ());
            (let rec collect_binders t =
               let uu____152 =
                 let uu____153 =
                   let uu____156 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____156
                    in
                 uu____153.FStar_Syntax_Syntax.n  in
               match uu____152 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____191) -> t1
                     | uu____200 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____201 = collect_binders rest  in
                   FStar_List.append bs uu____201
               | FStar_Syntax_Syntax.Tm_type uu____216 -> []
               | uu____223 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____247 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____247 FStar_Syntax_Util.name_binders
                in
             (let uu____273 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____273
              then
                let uu____274 =
                  let uu____275 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____275  in
                d uu____274
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____309 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____309 with
                | (sigelt,fv) ->
                    ((let uu____317 =
                        let uu____320 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____320
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____317);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____450  ->
                     match uu____450 with
                     | (t,b) ->
                         let uu____461 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____461))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____500 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____500))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____533 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____533)
                 in
              let uu____536 =
                let uu____553 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____577 =
                        let uu____580 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____580  in
                      FStar_Syntax_Util.arrow gamma uu____577  in
                    let uu____581 =
                      let uu____582 =
                        let uu____591 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____598 =
                          let uu____607 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____607]  in
                        uu____591 :: uu____598  in
                      FStar_List.append binders uu____582  in
                    FStar_Syntax_Util.abs uu____581 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____638 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____639 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____638, uu____639)  in
                match uu____553 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____679 =
                        let uu____680 =
                          let uu____697 =
                            let uu____708 =
                              FStar_List.map
                                (fun uu____730  ->
                                   match uu____730 with
                                   | (bv,uu____742) ->
                                       let uu____747 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____748 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____747, uu____748)) binders
                               in
                            let uu____749 =
                              let uu____756 =
                                let uu____761 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____762 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____761, uu____762)  in
                              let uu____763 =
                                let uu____770 =
                                  let uu____775 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____775)  in
                                [uu____770]  in
                              uu____756 :: uu____763  in
                            FStar_List.append uu____708 uu____749  in
                          (fv, uu____697)  in
                        FStar_Syntax_Syntax.Tm_app uu____680  in
                      mk1 uu____679  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____536 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____846 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____846
                       in
                    let ret1 =
                      let uu____850 =
                        let uu____851 =
                          let uu____854 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____854  in
                        FStar_Syntax_Util.residual_tot uu____851  in
                      FStar_Pervasives_Native.Some uu____850  in
                    let body =
                      let uu____858 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____858 ret1  in
                    let uu____861 =
                      let uu____862 = mk_all_implicit binders  in
                      let uu____869 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____862 uu____869  in
                    FStar_Syntax_Util.abs uu____861 body ret1  in
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
                      let uu____904 =
                        let uu____905 =
                          let uu____906 =
                            let uu____915 =
                              let uu____922 =
                                let uu____923 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____923
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____922  in
                            [uu____915]  in
                          let uu____936 =
                            let uu____939 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____939  in
                          FStar_Syntax_Util.arrow uu____906 uu____936  in
                        mk_gctx uu____905  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____904
                       in
                    let r =
                      let uu____941 =
                        let uu____942 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____942  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____941
                       in
                    let ret1 =
                      let uu____946 =
                        let uu____947 =
                          let uu____950 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____950  in
                        FStar_Syntax_Util.residual_tot uu____947  in
                      FStar_Pervasives_Native.Some uu____946  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____960 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____963 =
                          let uu____974 =
                            let uu____977 =
                              let uu____978 =
                                let uu____979 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____979
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____978  in
                            [uu____977]  in
                          FStar_List.append gamma_as_args uu____974  in
                        FStar_Syntax_Util.mk_app uu____960 uu____963  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____982 =
                      let uu____983 = mk_all_implicit binders  in
                      let uu____990 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____983 uu____990  in
                    FStar_Syntax_Util.abs uu____982 outer_body ret1  in
                  let c_app1 =
                    let uu____1026 = mk_lid "app"  in
                    register env1 uu____1026 c_app  in
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
                      let uu____1035 =
                        let uu____1044 =
                          let uu____1051 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1051  in
                        [uu____1044]  in
                      let uu____1064 =
                        let uu____1067 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1067  in
                      FStar_Syntax_Util.arrow uu____1035 uu____1064  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1070 =
                        let uu____1071 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1071  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1070
                       in
                    let ret1 =
                      let uu____1075 =
                        let uu____1076 =
                          let uu____1079 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1079  in
                        FStar_Syntax_Util.residual_tot uu____1076  in
                      FStar_Pervasives_Native.Some uu____1075  in
                    let uu____1080 =
                      let uu____1081 = mk_all_implicit binders  in
                      let uu____1088 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1081 uu____1088  in
                    let uu____1123 =
                      let uu____1126 =
                        let uu____1137 =
                          let uu____1140 =
                            let uu____1141 =
                              let uu____1152 =
                                let uu____1155 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1155]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1152
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1141  in
                          let uu____1164 =
                            let uu____1167 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1167]  in
                          uu____1140 :: uu____1164  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1137
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1126  in
                    FStar_Syntax_Util.abs uu____1080 uu____1123 ret1  in
                  let c_lift11 =
                    let uu____1177 = mk_lid "lift1"  in
                    register env1 uu____1177 c_lift1  in
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
                      let uu____1187 =
                        let uu____1196 =
                          let uu____1203 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1203  in
                        let uu____1204 =
                          let uu____1213 =
                            let uu____1220 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1220  in
                          [uu____1213]  in
                        uu____1196 :: uu____1204  in
                      let uu____1239 =
                        let uu____1242 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1242  in
                      FStar_Syntax_Util.arrow uu____1187 uu____1239  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1245 =
                        let uu____1246 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1246  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1245
                       in
                    let a2 =
                      let uu____1248 =
                        let uu____1249 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1249  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1248
                       in
                    let ret1 =
                      let uu____1253 =
                        let uu____1254 =
                          let uu____1257 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1257  in
                        FStar_Syntax_Util.residual_tot uu____1254  in
                      FStar_Pervasives_Native.Some uu____1253  in
                    let uu____1258 =
                      let uu____1259 = mk_all_implicit binders  in
                      let uu____1266 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1259 uu____1266  in
                    let uu____1309 =
                      let uu____1312 =
                        let uu____1323 =
                          let uu____1326 =
                            let uu____1327 =
                              let uu____1338 =
                                let uu____1341 =
                                  let uu____1342 =
                                    let uu____1353 =
                                      let uu____1356 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1356]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1353
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1342
                                   in
                                let uu____1365 =
                                  let uu____1368 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1368]  in
                                uu____1341 :: uu____1365  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1338
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1327  in
                          let uu____1377 =
                            let uu____1380 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1380]  in
                          uu____1326 :: uu____1377  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1323
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1312  in
                    FStar_Syntax_Util.abs uu____1258 uu____1309 ret1  in
                  let c_lift21 =
                    let uu____1390 = mk_lid "lift2"  in
                    register env1 uu____1390 c_lift2  in
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
                      let uu____1399 =
                        let uu____1408 =
                          let uu____1415 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1415  in
                        [uu____1408]  in
                      let uu____1428 =
                        let uu____1431 =
                          let uu____1432 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1432  in
                        FStar_Syntax_Syntax.mk_Total uu____1431  in
                      FStar_Syntax_Util.arrow uu____1399 uu____1428  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1437 =
                        let uu____1438 =
                          let uu____1441 =
                            let uu____1442 =
                              let uu____1451 =
                                let uu____1458 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1458
                                 in
                              [uu____1451]  in
                            let uu____1471 =
                              let uu____1474 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1474  in
                            FStar_Syntax_Util.arrow uu____1442 uu____1471  in
                          mk_ctx uu____1441  in
                        FStar_Syntax_Util.residual_tot uu____1438  in
                      FStar_Pervasives_Native.Some uu____1437  in
                    let e1 =
                      let uu____1476 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1476
                       in
                    let body =
                      let uu____1480 =
                        let uu____1481 =
                          let uu____1490 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1490]  in
                        FStar_List.append gamma uu____1481  in
                      let uu____1515 =
                        let uu____1518 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1521 =
                          let uu____1532 =
                            let uu____1533 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1533  in
                          let uu____1534 = args_of_binders1 gamma  in
                          uu____1532 :: uu____1534  in
                        FStar_Syntax_Util.mk_app uu____1518 uu____1521  in
                      FStar_Syntax_Util.abs uu____1480 uu____1515 ret1  in
                    let uu____1537 =
                      let uu____1538 = mk_all_implicit binders  in
                      let uu____1545 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1538 uu____1545  in
                    FStar_Syntax_Util.abs uu____1537 body ret1  in
                  let c_push1 =
                    let uu____1577 = mk_lid "push"  in
                    register env1 uu____1577 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1601 =
                        let uu____1602 =
                          let uu____1619 = args_of_binders1 binders  in
                          (c, uu____1619)  in
                        FStar_Syntax_Syntax.Tm_app uu____1602  in
                      mk1 uu____1601
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1647 =
                        let uu____1648 =
                          let uu____1657 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1664 =
                            let uu____1673 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1673]  in
                          uu____1657 :: uu____1664  in
                        let uu____1698 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1648 uu____1698  in
                      FStar_Syntax_Syntax.mk_Total uu____1647  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1702 =
                      let uu____1703 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1703  in
                    let uu____1718 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1722 =
                        let uu____1725 =
                          let uu____1736 =
                            let uu____1739 =
                              let uu____1740 =
                                let uu____1751 =
                                  let uu____1760 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1760  in
                                [uu____1751]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1740  in
                            [uu____1739]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1736
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1725  in
                      FStar_Syntax_Util.ascribe uu____1722
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1702 uu____1718
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1804 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1804 wp_if_then_else  in
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
                      let uu____1817 =
                        let uu____1828 =
                          let uu____1831 =
                            let uu____1832 =
                              let uu____1843 =
                                let uu____1846 =
                                  let uu____1847 =
                                    let uu____1858 =
                                      let uu____1867 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1867
                                       in
                                    [uu____1858]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1847
                                   in
                                [uu____1846]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1843
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1832  in
                          let uu____1892 =
                            let uu____1895 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1895]  in
                          uu____1831 :: uu____1892  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1828
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1817  in
                    let uu____1904 =
                      let uu____1905 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1905  in
                    FStar_Syntax_Util.abs uu____1904 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1921 = mk_lid "wp_assert"  in
                    register env1 uu____1921 wp_assert  in
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
                      let uu____1934 =
                        let uu____1945 =
                          let uu____1948 =
                            let uu____1949 =
                              let uu____1960 =
                                let uu____1963 =
                                  let uu____1964 =
                                    let uu____1975 =
                                      let uu____1984 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1984
                                       in
                                    [uu____1975]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1964
                                   in
                                [uu____1963]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1960
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1949  in
                          let uu____2009 =
                            let uu____2012 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2012]  in
                          uu____1948 :: uu____2009  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1945
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1934  in
                    let uu____2021 =
                      let uu____2022 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2022  in
                    FStar_Syntax_Util.abs uu____2021 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2038 = mk_lid "wp_assume"  in
                    register env1 uu____2038 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2049 =
                        let uu____2058 =
                          let uu____2065 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2065  in
                        [uu____2058]  in
                      let uu____2078 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2049 uu____2078  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2085 =
                        let uu____2096 =
                          let uu____2099 =
                            let uu____2100 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2100  in
                          let uu____2119 =
                            let uu____2122 =
                              let uu____2123 =
                                let uu____2134 =
                                  let uu____2137 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2137]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2134
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2123  in
                            [uu____2122]  in
                          uu____2099 :: uu____2119  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2096
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2085  in
                    let uu____2154 =
                      let uu____2155 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2155  in
                    FStar_Syntax_Util.abs uu____2154 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2171 = mk_lid "wp_close"  in
                    register env1 uu____2171 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2181 =
                      let uu____2182 =
                        let uu____2183 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2183
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2182  in
                    FStar_Pervasives_Native.Some uu____2181  in
                  let mk_forall1 x body =
                    let uu____2195 =
                      let uu____2202 =
                        let uu____2203 =
                          let uu____2220 =
                            let uu____2231 =
                              let uu____2240 =
                                let uu____2241 =
                                  let uu____2242 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2242]  in
                                FStar_Syntax_Util.abs uu____2241 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2240  in
                            [uu____2231]  in
                          (FStar_Syntax_Util.tforall, uu____2220)  in
                        FStar_Syntax_Syntax.Tm_app uu____2203  in
                      FStar_Syntax_Syntax.mk uu____2202  in
                    uu____2195 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2302 =
                      let uu____2303 = FStar_Syntax_Subst.compress t  in
                      uu____2303.FStar_Syntax_Syntax.n  in
                    match uu____2302 with
                    | FStar_Syntax_Syntax.Tm_type uu____2306 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2338  ->
                              match uu____2338 with
                              | (b,uu____2346) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2351 -> true  in
                  let rec is_monotonic t =
                    let uu____2362 =
                      let uu____2363 = FStar_Syntax_Subst.compress t  in
                      uu____2363.FStar_Syntax_Syntax.n  in
                    match uu____2362 with
                    | FStar_Syntax_Syntax.Tm_type uu____2366 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2398  ->
                              match uu____2398 with
                              | (b,uu____2406) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2411 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2485 =
                      let uu____2486 = FStar_Syntax_Subst.compress t1  in
                      uu____2486.FStar_Syntax_Syntax.n  in
                    match uu____2485 with
                    | FStar_Syntax_Syntax.Tm_type uu____2491 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2494);
                                      FStar_Syntax_Syntax.pos = uu____2495;
                                      FStar_Syntax_Syntax.vars = uu____2496;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2540 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2540
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2547 =
                              let uu____2550 =
                                let uu____2561 =
                                  let uu____2570 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2570  in
                                [uu____2561]  in
                              FStar_Syntax_Util.mk_app x uu____2550  in
                            let uu____2587 =
                              let uu____2590 =
                                let uu____2601 =
                                  let uu____2610 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2610  in
                                [uu____2601]  in
                              FStar_Syntax_Util.mk_app y uu____2590  in
                            mk_rel1 b uu____2547 uu____2587  in
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
                             let uu____2631 =
                               let uu____2634 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2637 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2634 uu____2637  in
                             let uu____2640 =
                               let uu____2643 =
                                 let uu____2646 =
                                   let uu____2657 =
                                     let uu____2666 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2666
                                      in
                                   [uu____2657]  in
                                 FStar_Syntax_Util.mk_app x uu____2646  in
                               let uu____2683 =
                                 let uu____2686 =
                                   let uu____2697 =
                                     let uu____2706 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2706
                                      in
                                   [uu____2697]  in
                                 FStar_Syntax_Util.mk_app y uu____2686  in
                               mk_rel1 b uu____2643 uu____2683  in
                             FStar_Syntax_Util.mk_imp uu____2631 uu____2640
                              in
                           let uu____2723 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2723)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2726);
                                      FStar_Syntax_Syntax.pos = uu____2727;
                                      FStar_Syntax_Syntax.vars = uu____2728;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2772 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2772
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2779 =
                              let uu____2782 =
                                let uu____2793 =
                                  let uu____2802 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2802  in
                                [uu____2793]  in
                              FStar_Syntax_Util.mk_app x uu____2782  in
                            let uu____2819 =
                              let uu____2822 =
                                let uu____2833 =
                                  let uu____2842 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2842  in
                                [uu____2833]  in
                              FStar_Syntax_Util.mk_app y uu____2822  in
                            mk_rel1 b uu____2779 uu____2819  in
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
                             let uu____2863 =
                               let uu____2866 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2869 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2866 uu____2869  in
                             let uu____2872 =
                               let uu____2875 =
                                 let uu____2878 =
                                   let uu____2889 =
                                     let uu____2898 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2898
                                      in
                                   [uu____2889]  in
                                 FStar_Syntax_Util.mk_app x uu____2878  in
                               let uu____2915 =
                                 let uu____2918 =
                                   let uu____2929 =
                                     let uu____2938 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2938
                                      in
                                   [uu____2929]  in
                                 FStar_Syntax_Util.mk_app y uu____2918  in
                               mk_rel1 b uu____2875 uu____2915  in
                             FStar_Syntax_Util.mk_imp uu____2863 uu____2872
                              in
                           let uu____2955 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2955)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___349_2994 = t1  in
                          let uu____2995 =
                            let uu____2996 =
                              let uu____3011 =
                                let uu____3014 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3014  in
                              ([binder], uu____3011)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2996  in
                          {
                            FStar_Syntax_Syntax.n = uu____2995;
                            FStar_Syntax_Syntax.pos =
                              (uu___349_2994.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___349_2994.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3037 ->
                        failwith "unhandled arrow"
                    | uu____3054 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env1 t
                         in
                      let uu____3089 =
                        let uu____3090 = FStar_Syntax_Subst.compress t1  in
                        uu____3090.FStar_Syntax_Syntax.n  in
                      match uu____3089 with
                      | FStar_Syntax_Syntax.Tm_type uu____3093 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3120 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3120
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3139 =
                                let uu____3140 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3140 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3139
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3169 =
                            let uu____3180 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3198  ->
                                     match uu____3198 with
                                     | (t2,q) ->
                                         let uu____3217 = project i x  in
                                         let uu____3220 = project i y  in
                                         mk_stronger t2 uu____3217 uu____3220)
                                args
                               in
                            match uu____3180 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3169 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
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
                                       let uu____3332 =
                                         let uu____3333 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3333  in
                                       FStar_Syntax_Syntax.gen_bv uu____3332
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3340 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3340) bvs
                             in
                          let body =
                            let uu____3342 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3345 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3342 uu____3345  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3354);
                                      FStar_Syntax_Syntax.pos = uu____3355;
                                      FStar_Syntax_Syntax.vars = uu____3356;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3400  ->
                                   match uu____3400 with
                                   | (bv,q) ->
                                       let uu____3413 =
                                         let uu____3414 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3414  in
                                       FStar_Syntax_Syntax.gen_bv uu____3413
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3421 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3421) bvs
                             in
                          let body =
                            let uu____3423 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3426 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3423 uu____3426  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3433 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3435 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3438 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3441 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3435 uu____3438 uu____3441  in
                    let uu____3444 =
                      let uu____3445 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3445  in
                    FStar_Syntax_Util.abs uu____3444 body ret_tot_type  in
                  let stronger1 =
                    let uu____3477 = mk_lid "stronger"  in
                    register env1 uu____3477 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3483 = FStar_Util.prefix gamma  in
                    match uu____3483 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3548 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3548
                             in
                          let uu____3553 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3553 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3563 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3563  in
                              let guard_free1 =
                                let uu____3575 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3575  in
                              let pat =
                                let uu____3579 =
                                  let uu____3590 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3590]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3579
                                 in
                              let pattern_guarded_body =
                                let uu____3618 =
                                  let uu____3619 =
                                    let uu____3626 =
                                      let uu____3627 =
                                        let uu____3640 =
                                          let uu____3651 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3651]  in
                                        [uu____3640]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3627
                                       in
                                    (body, uu____3626)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3619  in
                                mk1 uu____3618  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3698 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3706 =
                            let uu____3709 =
                              let uu____3710 =
                                let uu____3713 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3716 =
                                  let uu____3727 = args_of_binders1 wp_args
                                     in
                                  let uu____3730 =
                                    let uu____3733 =
                                      let uu____3734 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3734
                                       in
                                    [uu____3733]  in
                                  FStar_List.append uu____3727 uu____3730  in
                                FStar_Syntax_Util.mk_app uu____3713
                                  uu____3716
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3710  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3709
                             in
                          FStar_Syntax_Util.abs gamma uu____3706
                            ret_gtot_type
                           in
                        let uu____3735 =
                          let uu____3736 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3736  in
                        FStar_Syntax_Util.abs uu____3735 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3752 = mk_lid "wp_ite"  in
                    register env1 uu____3752 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3758 = FStar_Util.prefix gamma  in
                    match uu____3758 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3815 =
                            let uu____3816 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3823 =
                              let uu____3834 =
                                let uu____3843 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3843  in
                              [uu____3834]  in
                            FStar_Syntax_Util.mk_app uu____3816 uu____3823
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3815
                           in
                        let uu____3860 =
                          let uu____3861 =
                            let uu____3870 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3870 gamma  in
                          FStar_List.append binders uu____3861  in
                        FStar_Syntax_Util.abs uu____3860 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3892 = mk_lid "null_wp"  in
                    register env1 uu____3892 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3903 =
                        let uu____3914 =
                          let uu____3917 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3918 =
                            let uu____3921 =
                              let uu____3922 =
                                let uu____3933 =
                                  let uu____3942 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3942  in
                                [uu____3933]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3922
                               in
                            let uu____3959 =
                              let uu____3962 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3962]  in
                            uu____3921 :: uu____3959  in
                          uu____3917 :: uu____3918  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3914
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3903  in
                    let uu____3971 =
                      let uu____3972 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3972  in
                    FStar_Syntax_Util.abs uu____3971 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3988 = mk_lid "wp_trivial"  in
                    register env1 uu____3988 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3993 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3993
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____4000 =
                      let uu____4001 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____4001  in
                    let uu____4053 =
                      let uu___350_4054 = ed  in
                      let uu____4055 =
                        let uu____4056 = c wp_if_then_else2  in
                        ([], uu____4056)  in
                      let uu____4063 =
                        let uu____4064 = c wp_ite2  in ([], uu____4064)  in
                      let uu____4071 =
                        let uu____4072 = c stronger2  in ([], uu____4072)  in
                      let uu____4079 =
                        let uu____4080 = c wp_close2  in ([], uu____4080)  in
                      let uu____4087 =
                        let uu____4088 = c wp_assert2  in ([], uu____4088)
                         in
                      let uu____4095 =
                        let uu____4096 = c wp_assume2  in ([], uu____4096)
                         in
                      let uu____4103 =
                        let uu____4104 = c null_wp2  in ([], uu____4104)  in
                      let uu____4111 =
                        let uu____4112 = c wp_trivial2  in ([], uu____4112)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___350_4054.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___350_4054.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___350_4054.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___350_4054.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___350_4054.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___350_4054.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___350_4054.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____4055;
                        FStar_Syntax_Syntax.ite_wp = uu____4063;
                        FStar_Syntax_Syntax.stronger = uu____4071;
                        FStar_Syntax_Syntax.close_wp = uu____4079;
                        FStar_Syntax_Syntax.assert_p = uu____4087;
                        FStar_Syntax_Syntax.assume_p = uu____4095;
                        FStar_Syntax_Syntax.null_wp = uu____4103;
                        FStar_Syntax_Syntax.trivial = uu____4111;
                        FStar_Syntax_Syntax.repr =
                          (uu___350_4054.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___350_4054.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___350_4054.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___350_4054.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___350_4054.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____4000, uu____4053)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___351_4134 = dmff_env  in
      {
        env = env';
        subst = (uu___351_4134.subst);
        tc_const = (uu___351_4134.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4151 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4165 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___337_4177  ->
    match uu___337_4177 with
    | FStar_Syntax_Syntax.Total (t,uu____4179) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___336_4192  ->
                match uu___336_4192 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4193 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____4195 =
          let uu____4196 =
            let uu____4197 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____4197
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____4196  in
        failwith uu____4195
    | FStar_Syntax_Syntax.GTotal uu____4198 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___338_4211  ->
    match uu___338_4211 with
    | N t ->
        let uu____4213 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4213
    | M t ->
        let uu____4215 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4215
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____4221,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____4223;
                      FStar_Syntax_Syntax.vars = uu____4224;_})
        -> nm_of_comp n2
    | uu____4245 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4255 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____4255 with | M uu____4256 -> true | N uu____4257 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4263 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4277 =
        let uu____4286 =
          let uu____4293 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4293  in
        [uu____4286]  in
      let uu____4312 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4277 uu____4312  in
    let uu____4315 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4315
  
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
        let uu____4356 =
          let uu____4357 =
            let uu____4372 =
              let uu____4381 =
                let uu____4388 =
                  let uu____4389 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4389  in
                let uu____4390 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4388, uu____4390)  in
              [uu____4381]  in
            let uu____4407 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4372, uu____4407)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4357  in
        mk1 uu____4356

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____4447) ->
          let binders1 =
            FStar_List.map
              (fun uu____4493  ->
                 match uu____4493 with
                 | (bv,aqual) ->
                     let uu____4512 =
                       let uu___352_4513 = bv  in
                       let uu____4514 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___352_4513.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___352_4513.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4514
                       }  in
                     (uu____4512, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4519,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____4521);
                             FStar_Syntax_Syntax.pos = uu____4522;
                             FStar_Syntax_Syntax.vars = uu____4523;_})
               ->
               let uu____4552 =
                 let uu____4553 =
                   let uu____4568 =
                     let uu____4571 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4571  in
                   (binders1, uu____4568)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____4553  in
               mk1 uu____4552
           | uu____4582 ->
               let uu____4583 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4583 with
                | N hn ->
                    let uu____4585 =
                      let uu____4586 =
                        let uu____4601 =
                          let uu____4604 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4604  in
                        (binders1, uu____4601)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4586  in
                    mk1 uu____4585
                | M a ->
                    let uu____4616 =
                      let uu____4617 =
                        let uu____4632 =
                          let uu____4641 =
                            let uu____4650 =
                              let uu____4657 =
                                let uu____4658 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4658  in
                              let uu____4659 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4657, uu____4659)  in
                            [uu____4650]  in
                          FStar_List.append binders1 uu____4641  in
                        let uu____4682 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4632, uu____4682)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4617  in
                    mk1 uu____4616))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4770 = f x  in
                    FStar_Util.string_builder_append strb uu____4770);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4777 = f x1  in
                         FStar_Util.string_builder_append strb uu____4777))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4779 =
              let uu____4784 =
                let uu____4785 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4786 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4785 uu____4786
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4784)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4779  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4802 =
              let uu____4803 = FStar_Syntax_Subst.compress ty  in
              uu____4803.FStar_Syntax_Syntax.n  in
            match uu____4802 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4828 =
                  let uu____4829 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4829  in
                if uu____4828
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____4863 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____4863 s  in
                       let uu____4866 =
                         let uu____4867 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____4867  in
                       if uu____4866
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____4870 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____4870 with
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
                         let ct = FStar_Syntax_Util.comp_result c1  in
                         (non_dependent_or_raise s ct;
                          (let k = n1 - (FStar_List.length binders1)  in
                           if k > (Prims.parse_int "0")
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found  -> false)
            | uu____4926 ->
                ((let uu____4928 =
                    let uu____4933 =
                      let uu____4934 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4934
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4933)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4928);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4945 =
              let uu____4946 = FStar_Syntax_Subst.compress head2  in
              uu____4946.FStar_Syntax_Syntax.n  in
            match uu____4945 with
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
                  (let uu____4951 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4951)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4953 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4953 with
                 | ((uu____4962,ty),uu____4964) ->
                     let uu____4969 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4969
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.env t1
                          in
                       let uu____4979 =
                         let uu____4980 = FStar_Syntax_Subst.compress res  in
                         uu____4980.FStar_Syntax_Syntax.n  in
                       (match uu____4979 with
                        | FStar_Syntax_Syntax.Tm_app uu____4983 -> true
                        | uu____5000 ->
                            ((let uu____5002 =
                                let uu____5007 =
                                  let uu____5008 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____5008
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____5007)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____5002);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____5010 -> true
            | FStar_Syntax_Syntax.Tm_name uu____5011 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5013) ->
                is_valid_application t2
            | uu____5018 -> false  in
          let uu____5019 = is_valid_application head1  in
          if uu____5019
          then
            let uu____5020 =
              let uu____5021 =
                let uu____5038 =
                  FStar_List.map
                    (fun uu____5067  ->
                       match uu____5067 with
                       | (t2,qual) ->
                           let uu____5092 = star_type' env t2  in
                           (uu____5092, qual)) args
                   in
                (head1, uu____5038)  in
              FStar_Syntax_Syntax.Tm_app uu____5021  in
            mk1 uu____5020
          else
            (let uu____5108 =
               let uu____5113 =
                 let uu____5114 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5114
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5113)  in
             FStar_Errors.raise_err uu____5108)
      | FStar_Syntax_Syntax.Tm_bvar uu____5115 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5116 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5117 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5118 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5146 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5146 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___355_5154 = env  in
                 let uu____5155 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____5155;
                   subst = (uu___355_5154.subst);
                   tc_const = (uu___355_5154.tc_const)
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
               ((let uu___356_5177 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___356_5177.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___356_5177.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5184 =
            let uu____5185 =
              let uu____5192 = star_type' env t2  in (uu____5192, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5185  in
          mk1 uu____5184
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5244 =
            let uu____5245 =
              let uu____5272 = star_type' env e  in
              let uu____5275 =
                let uu____5292 =
                  let uu____5301 = star_type' env t2  in
                  FStar_Util.Inl uu____5301  in
                (uu____5292, FStar_Pervasives_Native.None)  in
              (uu____5272, uu____5275, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5245  in
          mk1 uu____5244
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5389 =
            let uu____5390 =
              let uu____5417 = star_type' env e  in
              let uu____5420 =
                let uu____5437 =
                  let uu____5446 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5446  in
                (uu____5437, FStar_Pervasives_Native.None)  in
              (uu____5417, uu____5420, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5390  in
          mk1 uu____5389
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5487,(uu____5488,FStar_Pervasives_Native.Some uu____5489),uu____5490)
          ->
          let uu____5539 =
            let uu____5544 =
              let uu____5545 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5545
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5544)  in
          FStar_Errors.raise_err uu____5539
      | FStar_Syntax_Syntax.Tm_refine uu____5546 ->
          let uu____5553 =
            let uu____5558 =
              let uu____5559 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5559
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5558)  in
          FStar_Errors.raise_err uu____5553
      | FStar_Syntax_Syntax.Tm_uinst uu____5560 ->
          let uu____5567 =
            let uu____5572 =
              let uu____5573 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5573
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5572)  in
          FStar_Errors.raise_err uu____5567
      | FStar_Syntax_Syntax.Tm_quoted uu____5574 ->
          let uu____5581 =
            let uu____5586 =
              let uu____5587 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5587
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5586)  in
          FStar_Errors.raise_err uu____5581
      | FStar_Syntax_Syntax.Tm_constant uu____5588 ->
          let uu____5589 =
            let uu____5594 =
              let uu____5595 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5595
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5594)  in
          FStar_Errors.raise_err uu____5589
      | FStar_Syntax_Syntax.Tm_match uu____5596 ->
          let uu____5619 =
            let uu____5624 =
              let uu____5625 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5625
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5624)  in
          FStar_Errors.raise_err uu____5619
      | FStar_Syntax_Syntax.Tm_let uu____5626 ->
          let uu____5639 =
            let uu____5644 =
              let uu____5645 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5645
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5644)  in
          FStar_Errors.raise_err uu____5639
      | FStar_Syntax_Syntax.Tm_uvar uu____5646 ->
          let uu____5659 =
            let uu____5664 =
              let uu____5665 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5665
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5664)  in
          FStar_Errors.raise_err uu____5659
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5666 =
            let uu____5671 =
              let uu____5672 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5672
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5671)  in
          FStar_Errors.raise_err uu____5666
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5674 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5674
      | FStar_Syntax_Syntax.Tm_delayed uu____5677 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___340_5706  ->
    match uu___340_5706 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___339_5713  ->
                match uu___339_5713 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5714 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5720 =
      let uu____5721 = FStar_Syntax_Subst.compress t  in
      uu____5721.FStar_Syntax_Syntax.n  in
    match uu____5720 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5751 =
            let uu____5752 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5752  in
          is_C uu____5751  in
        if r
        then
          ((let uu____5774 =
              let uu____5775 =
                FStar_List.for_all
                  (fun uu____5785  ->
                     match uu____5785 with | (h,uu____5793) -> is_C h) args
                 in
              Prims.op_Negation uu____5775  in
            if uu____5774 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5801 =
              let uu____5802 =
                FStar_List.for_all
                  (fun uu____5813  ->
                     match uu____5813 with
                     | (h,uu____5821) ->
                         let uu____5826 = is_C h  in
                         Prims.op_Negation uu____5826) args
                 in
              Prims.op_Negation uu____5802  in
            if uu____5801 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5850 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5850 with
         | M t1 ->
             ((let uu____5853 = is_C t1  in
               if uu____5853 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5857) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5863) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5869,uu____5870) -> is_C t1
    | uu____5911 -> false
  
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
          let uu____5944 =
            let uu____5945 =
              let uu____5962 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____5965 =
                let uu____5976 =
                  let uu____5985 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____5985)  in
                [uu____5976]  in
              (uu____5962, uu____5965)  in
            FStar_Syntax_Syntax.Tm_app uu____5945  in
          mk1 uu____5944  in
        let uu____6020 =
          let uu____6021 = FStar_Syntax_Syntax.mk_binder p  in [uu____6021]
           in
        FStar_Syntax_Util.abs uu____6020 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___341_6044  ->
    match uu___341_6044 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6045 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____6280 =
          match uu____6280 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6317 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6319 =
                       let uu____6320 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6320  in
                     Prims.op_Negation uu____6319)
                   in
                if uu____6317
                then
                  let uu____6321 =
                    let uu____6326 =
                      let uu____6327 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6328 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6329 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6327 uu____6328 uu____6329
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6326)  in
                  FStar_Errors.raise_err uu____6321
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6350 = mk_return env t1 s_e  in
                     ((M t1), uu____6350, u_e)))
               | (M t1,N t2) ->
                   let uu____6357 =
                     let uu____6362 =
                       let uu____6363 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6364 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6365 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6363 uu____6364 uu____6365
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6362)
                      in
                   FStar_Errors.raise_err uu____6357)
           in
        let ensure_m env1 e2 =
          let strip_m uu___342_6414 =
            match uu___342_6414 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6430 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6450 =
                let uu____6455 =
                  let uu____6456 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6456
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6455)  in
              FStar_Errors.raise_error uu____6450 e2.FStar_Syntax_Syntax.pos
          | M uu____6463 ->
              let uu____6464 = check env1 e2 context_nm  in
              strip_m uu____6464
           in
        let uu____6471 =
          let uu____6472 = FStar_Syntax_Subst.compress e  in
          uu____6472.FStar_Syntax_Syntax.n  in
        match uu____6471 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6481 ->
            let uu____6482 = infer env e  in return_if uu____6482
        | FStar_Syntax_Syntax.Tm_name uu____6489 ->
            let uu____6490 = infer env e  in return_if uu____6490
        | FStar_Syntax_Syntax.Tm_fvar uu____6497 ->
            let uu____6498 = infer env e  in return_if uu____6498
        | FStar_Syntax_Syntax.Tm_abs uu____6505 ->
            let uu____6524 = infer env e  in return_if uu____6524
        | FStar_Syntax_Syntax.Tm_constant uu____6531 ->
            let uu____6532 = infer env e  in return_if uu____6532
        | FStar_Syntax_Syntax.Tm_quoted uu____6539 ->
            let uu____6546 = infer env e  in return_if uu____6546
        | FStar_Syntax_Syntax.Tm_app uu____6553 ->
            let uu____6570 = infer env e  in return_if uu____6570
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6578 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6578 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6640) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6646) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6652,uu____6653) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6694 ->
            let uu____6707 =
              let uu____6708 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6708  in
            failwith uu____6707
        | FStar_Syntax_Syntax.Tm_type uu____6715 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6722 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6743 ->
            let uu____6750 =
              let uu____6751 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6751  in
            failwith uu____6750
        | FStar_Syntax_Syntax.Tm_uvar uu____6758 ->
            let uu____6771 =
              let uu____6772 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6772  in
            failwith uu____6771
        | FStar_Syntax_Syntax.Tm_delayed uu____6779 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6808 =
              let uu____6809 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6809  in
            failwith uu____6808

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env
         in
      let uu____6837 =
        let uu____6838 = FStar_Syntax_Subst.compress e  in
        uu____6838.FStar_Syntax_Syntax.n  in
      match uu____6837 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6856 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6856
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6907;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____6908;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6914 =
                  let uu___357_6915 = rc  in
                  let uu____6916 =
                    let uu____6921 =
                      let uu____6924 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____6924  in
                    FStar_Pervasives_Native.Some uu____6921  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___357_6915.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6916;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___357_6915.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____6914
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___358_6936 = env  in
            let uu____6937 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____6937;
              subst = (uu___358_6936.subst);
              tc_const = (uu___358_6936.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____6963  ->
                 match uu____6963 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___359_6986 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___359_6986.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___359_6986.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____6987 =
            FStar_List.fold_left
              (fun uu____7018  ->
                 fun uu____7019  ->
                   match (uu____7018, uu____7019) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7077 = is_C c  in
                       if uu____7077
                       then
                         let xw =
                           let uu____7085 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7085
                            in
                         let x =
                           let uu___360_7087 = bv  in
                           let uu____7088 =
                             let uu____7091 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7091  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___360_7087.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___360_7087.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7088
                           }  in
                         let env3 =
                           let uu___361_7093 = env2  in
                           let uu____7094 =
                             let uu____7097 =
                               let uu____7098 =
                                 let uu____7105 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7105)  in
                               FStar_Syntax_Syntax.NT uu____7098  in
                             uu____7097 :: (env2.subst)  in
                           {
                             env = (uu___361_7093.env);
                             subst = uu____7094;
                             tc_const = (uu___361_7093.tc_const)
                           }  in
                         let uu____7110 =
                           let uu____7113 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7114 =
                             let uu____7117 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7117 :: acc  in
                           uu____7113 :: uu____7114  in
                         (env3, uu____7110)
                       else
                         (let x =
                            let uu___362_7122 = bv  in
                            let uu____7123 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___362_7122.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___362_7122.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7123
                            }  in
                          let uu____7126 =
                            let uu____7129 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7129 :: acc  in
                          (env2, uu____7126))) (env1, []) binders1
             in
          (match uu____6987 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7149 =
                 let check_what =
                   let uu____7175 = is_monadic rc_opt1  in
                   if uu____7175 then check_m else check_n  in
                 let uu____7189 = check_what env2 body1  in
                 match uu____7189 with
                 | (t,s_body,u_body) ->
                     let uu____7209 =
                       let uu____7212 =
                         let uu____7213 = is_monadic rc_opt1  in
                         if uu____7213 then M t else N t  in
                       comp_of_nm uu____7212  in
                     (uu____7209, s_body, u_body)
                  in
               (match uu____7149 with
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
                                 let uu____7250 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___343_7254  ->
                                           match uu___343_7254 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7255 -> false))
                                    in
                                 if uu____7250
                                 then
                                   let uu____7256 =
                                     FStar_List.filter
                                       (fun uu___344_7260  ->
                                          match uu___344_7260 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7261 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7256
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7270 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___345_7274  ->
                                         match uu___345_7274 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7275 -> false))
                                  in
                               if uu____7270
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___346_7282  ->
                                        match uu___346_7282 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7283 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7284 =
                                   let uu____7285 =
                                     let uu____7290 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7290
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7285 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____7284
                               else
                                 (let uu____7296 =
                                    let uu___363_7297 = rc  in
                                    let uu____7298 =
                                      let uu____7303 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7303
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___363_7297.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7298;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___363_7297.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7296))
                       in
                    let uu____7308 =
                      let comp1 =
                        let uu____7316 = is_monadic rc_opt1  in
                        let uu____7317 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7316 uu____7317
                         in
                      let uu____7318 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7318,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7308 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7356 =
                             let uu____7357 =
                               let uu____7376 =
                                 let uu____7379 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7379 s_rc_opt  in
                               (s_binders1, s_body1, uu____7376)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7357  in
                           mk1 uu____7356  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7399 =
                             let uu____7400 =
                               let uu____7419 =
                                 let uu____7422 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7422 u_rc_opt  in
                               (u_binders2, u_body2, uu____7419)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7400  in
                           mk1 uu____7399  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7438;_};
            FStar_Syntax_Syntax.fv_delta = uu____7439;
            FStar_Syntax_Syntax.fv_qual = uu____7440;_}
          ->
          let uu____7443 =
            let uu____7448 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7448  in
          (match uu____7443 with
           | (uu____7479,t) ->
               let uu____7481 =
                 let uu____7482 = normalize1 t  in N uu____7482  in
               (uu____7481, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7483;
             FStar_Syntax_Syntax.vars = uu____7484;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7563 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7563 with
           | (unary_op,uu____7587) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7658;
             FStar_Syntax_Syntax.vars = uu____7659;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7755 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7755 with
           | (unary_op,uu____7779) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7858;
             FStar_Syntax_Syntax.vars = uu____7859;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____7897 = infer env a  in
          (match uu____7897 with
           | (t,s,u) ->
               let uu____7913 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7913 with
                | (head1,uu____7937) ->
                    let uu____7962 =
                      let uu____7963 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____7963  in
                    let uu____7964 =
                      let uu____7965 =
                        let uu____7966 =
                          let uu____7983 =
                            let uu____7994 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7994]  in
                          (head1, uu____7983)  in
                        FStar_Syntax_Syntax.Tm_app uu____7966  in
                      mk1 uu____7965  in
                    let uu____8031 =
                      let uu____8032 =
                        let uu____8033 =
                          let uu____8050 =
                            let uu____8061 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8061]  in
                          (head1, uu____8050)  in
                        FStar_Syntax_Syntax.Tm_app uu____8033  in
                      mk1 uu____8032  in
                    (uu____7962, uu____7964, uu____8031)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8098;
             FStar_Syntax_Syntax.vars = uu____8099;_},(a1,uu____8101)::a2::[])
          ->
          let uu____8157 = infer env a1  in
          (match uu____8157 with
           | (t,s,u) ->
               let uu____8173 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8173 with
                | (head1,uu____8197) ->
                    let uu____8222 =
                      let uu____8223 =
                        let uu____8224 =
                          let uu____8241 =
                            let uu____8252 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8252; a2]  in
                          (head1, uu____8241)  in
                        FStar_Syntax_Syntax.Tm_app uu____8224  in
                      mk1 uu____8223  in
                    let uu____8297 =
                      let uu____8298 =
                        let uu____8299 =
                          let uu____8316 =
                            let uu____8327 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8327; a2]  in
                          (head1, uu____8316)  in
                        FStar_Syntax_Syntax.Tm_app uu____8299  in
                      mk1 uu____8298  in
                    (t, uu____8222, uu____8297)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8372;
             FStar_Syntax_Syntax.vars = uu____8373;_},uu____8374)
          ->
          let uu____8399 =
            let uu____8404 =
              let uu____8405 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8405
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8404)  in
          FStar_Errors.raise_error uu____8399 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8412;
             FStar_Syntax_Syntax.vars = uu____8413;_},uu____8414)
          ->
          let uu____8439 =
            let uu____8444 =
              let uu____8445 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8445
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8444)  in
          FStar_Errors.raise_error uu____8439 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8478 = check_n env head1  in
          (match uu____8478 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8500 =
                   let uu____8501 = FStar_Syntax_Subst.compress t  in
                   uu____8501.FStar_Syntax_Syntax.n  in
                 match uu____8500 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8504 -> true
                 | uu____8519 -> false  in
               let rec flatten1 t =
                 let uu____8540 =
                   let uu____8541 = FStar_Syntax_Subst.compress t  in
                   uu____8541.FStar_Syntax_Syntax.n  in
                 match uu____8540 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8560);
                                FStar_Syntax_Syntax.pos = uu____8561;
                                FStar_Syntax_Syntax.vars = uu____8562;_})
                     when is_arrow t1 ->
                     let uu____8591 = flatten1 t1  in
                     (match uu____8591 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8691,uu____8692)
                     -> flatten1 e1
                 | uu____8733 ->
                     let uu____8734 =
                       let uu____8739 =
                         let uu____8740 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____8740
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____8739)  in
                     FStar_Errors.raise_err uu____8734
                  in
               let uu____8755 = flatten1 t_head  in
               (match uu____8755 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____8829 =
                          let uu____8834 =
                            let uu____8835 = FStar_Util.string_of_int n1  in
                            let uu____8842 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____8853 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____8835 uu____8842 uu____8853
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____8834)
                           in
                        FStar_Errors.raise_err uu____8829)
                     else ();
                     (let uu____8861 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____8861 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____8914 args1 =
                            match uu____8914 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9014 =
                                       let uu____9015 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____9015.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____9014
                                 | (binders3,[]) ->
                                     let uu____9053 =
                                       let uu____9054 =
                                         let uu____9057 =
                                           let uu____9058 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9058
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9057
                                          in
                                       uu____9054.FStar_Syntax_Syntax.n  in
                                     (match uu____9053 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9091 =
                                            let uu____9092 =
                                              let uu____9093 =
                                                let uu____9108 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9108)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9093
                                               in
                                            mk1 uu____9092  in
                                          N uu____9091
                                      | uu____9121 -> failwith "wat?")
                                 | ([],uu____9122::uu____9123) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9175)::binders3,(arg,uu____9178)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9265 = FStar_List.splitAt n' binders1  in
                          (match uu____9265 with
                           | (binders2,uu____9303) ->
                               let uu____9336 =
                                 let uu____9359 =
                                   FStar_List.map2
                                     (fun uu____9421  ->
                                        fun uu____9422  ->
                                          match (uu____9421, uu____9422) with
                                          | ((bv,uu____9470),(arg,q)) ->
                                              let uu____9499 =
                                                let uu____9500 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9500.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9499 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9521 ->
                                                   let uu____9522 =
                                                     let uu____9529 =
                                                       star_type' env arg  in
                                                     (uu____9529, q)  in
                                                   (uu____9522, [(arg, q)])
                                               | uu____9566 ->
                                                   let uu____9567 =
                                                     check_n env arg  in
                                                   (match uu____9567 with
                                                    | (uu____9592,s_arg,u_arg)
                                                        ->
                                                        let uu____9595 =
                                                          let uu____9604 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9604
                                                          then
                                                            let uu____9613 =
                                                              let uu____9620
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9620, q)
                                                               in
                                                            [uu____9613;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9595))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9359  in
                               (match uu____9336 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____9747 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____9760 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____9747, uu____9760)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____9826) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____9832) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9838,uu____9839) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____9881 = let uu____9882 = env.tc_const c  in N uu____9882
             in
          (uu____9881, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____9889 ->
          let uu____9902 =
            let uu____9903 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____9903  in
          failwith uu____9902
      | FStar_Syntax_Syntax.Tm_type uu____9910 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____9917 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____9938 ->
          let uu____9945 =
            let uu____9946 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____9946  in
          failwith uu____9945
      | FStar_Syntax_Syntax.Tm_uvar uu____9953 ->
          let uu____9966 =
            let uu____9967 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____9967  in
          failwith uu____9966
      | FStar_Syntax_Syntax.Tm_delayed uu____9974 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____10003 =
            let uu____10004 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____10004  in
          failwith uu____10003

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____10051 = check_n env e0  in
          match uu____10051 with
          | (uu____10064,s_e0,u_e0) ->
              let uu____10067 =
                let uu____10096 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10157 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10157 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___364_10199 = env  in
                             let uu____10200 =
                               let uu____10201 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____10201
                                in
                             {
                               env = uu____10200;
                               subst = (uu___364_10199.subst);
                               tc_const = (uu___364_10199.tc_const)
                             }  in
                           let uu____10204 = f env1 body  in
                           (match uu____10204 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10276 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10096  in
              (match uu____10067 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10380 = FStar_List.hd nms  in
                     match uu____10380 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___347_10388  ->
                          match uu___347_10388 with
                          | M uu____10389 -> true
                          | uu____10390 -> false) nms
                      in
                   let uu____10391 =
                     let uu____10428 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10518  ->
                              match uu____10518 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____10695 =
                                         check env original_body (M t2)  in
                                       (match uu____10695 with
                                        | (uu____10732,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____10771,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10428  in
                   (match uu____10391 with
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
                              (fun uu____10955  ->
                                 match uu____10955 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____11006 =
                                         let uu____11007 =
                                           let uu____11024 =
                                             let uu____11035 =
                                               let uu____11044 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11047 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11044, uu____11047)  in
                                             [uu____11035]  in
                                           (s_body, uu____11024)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____11007
                                          in
                                       mk1 uu____11006  in
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
                            let uu____11181 =
                              let uu____11182 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11182]  in
                            let uu____11201 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11181 uu____11201
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11225 =
                              let uu____11234 =
                                let uu____11241 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11241
                                 in
                              [uu____11234]  in
                            let uu____11260 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11225 uu____11260
                             in
                          let uu____11263 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11302 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11263, uu____11302)
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
                           let uu____11411 =
                             let uu____11412 =
                               let uu____11413 =
                                 let uu____11440 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11440,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11413
                                in
                             mk1 uu____11412  in
                           let uu____11499 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11411, uu____11499))))

and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
                 FStar_Pervasives_Native.tuple3)
            ->
            (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple3)
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
              let uu____11564 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11564]  in
            let uu____11583 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11583 with
            | (x_binders1,e21) ->
                let uu____11596 = infer env e1  in
                (match uu____11596 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____11613 = is_C t1  in
                       if uu____11613
                       then
                         let uu___365_11614 = binding  in
                         let uu____11615 =
                           let uu____11618 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____11618  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___365_11614.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___365_11614.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11615;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___365_11614.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___365_11614.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___365_11614.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___365_11614.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___366_11621 = env  in
                       let uu____11622 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___367_11624 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___367_11624.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___367_11624.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____11622;
                         subst = (uu___366_11621.subst);
                         tc_const = (uu___366_11621.tc_const)
                       }  in
                     let uu____11625 = proceed env1 e21  in
                     (match uu____11625 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___368_11642 = binding  in
                            let uu____11643 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___368_11642.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___368_11642.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11643;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___368_11642.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___368_11642.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___368_11642.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___368_11642.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____11646 =
                            let uu____11647 =
                              let uu____11648 =
                                let uu____11661 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___369_11675 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___369_11675.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___369_11675.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___369_11675.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___369_11675.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___369_11675.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___369_11675.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11661)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11648  in
                            mk1 uu____11647  in
                          let uu____11676 =
                            let uu____11677 =
                              let uu____11678 =
                                let uu____11691 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___370_11705 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___370_11705.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___370_11705.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___370_11705.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___370_11705.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___370_11705.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___370_11705.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11691)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11678  in
                            mk1 uu____11677  in
                          (nm_rec, uu____11646, uu____11676))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___371_11710 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___371_11710.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___371_11710.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___371_11710.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___371_11710.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___371_11710.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___372_11712 = env  in
                       let uu____11713 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___373_11715 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___373_11715.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___373_11715.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____11713;
                         subst = (uu___372_11712.subst);
                         tc_const = (uu___372_11712.tc_const)
                       }  in
                     let uu____11716 = ensure_m env1 e21  in
                     (match uu____11716 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____11739 =
                              let uu____11740 =
                                let uu____11757 =
                                  let uu____11768 =
                                    let uu____11777 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____11780 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____11777, uu____11780)  in
                                  [uu____11768]  in
                                (s_e2, uu____11757)  in
                              FStar_Syntax_Syntax.Tm_app uu____11740  in
                            mk1 uu____11739  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____11821 =
                              let uu____11822 =
                                let uu____11839 =
                                  let uu____11850 =
                                    let uu____11859 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____11859)  in
                                  [uu____11850]  in
                                (s_e1, uu____11839)  in
                              FStar_Syntax_Syntax.Tm_app uu____11822  in
                            mk1 uu____11821  in
                          let uu____11894 =
                            let uu____11895 =
                              let uu____11896 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11896]  in
                            FStar_Syntax_Util.abs uu____11895 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____11915 =
                            let uu____11916 =
                              let uu____11917 =
                                let uu____11930 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___374_11944 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___374_11944.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___374_11944.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___374_11944.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___374_11944.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___374_11944.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___374_11944.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11930)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11917  in
                            mk1 uu____11916  in
                          ((M t2), uu____11894, uu____11915)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____11954 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____11954  in
      let uu____11955 = check env e mn  in
      match uu____11955 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____11971 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____11993 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____11993  in
      let uu____11994 = check env e mn  in
      match uu____11994 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____12010 -> failwith "[check_m]: impossible"

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
        (let uu____12042 =
           let uu____12043 = is_C c  in Prims.op_Negation uu____12043  in
         if uu____12042 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12053 =
           let uu____12054 = FStar_Syntax_Subst.compress c  in
           uu____12054.FStar_Syntax_Syntax.n  in
         match uu____12053 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12083 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12083 with
              | (wp_head,wp_args) ->
                  ((let uu____12127 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12145 =
                           let uu____12146 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12146
                            in
                         Prims.op_Negation uu____12145)
                       in
                    if uu____12127 then failwith "mismatch" else ());
                   (let uu____12156 =
                      let uu____12157 =
                        let uu____12174 =
                          FStar_List.map2
                            (fun uu____12212  ->
                               fun uu____12213  ->
                                 match (uu____12212, uu____12213) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12274 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12274
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12277 =
                                         let uu____12278 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12278 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12277
                                       then
                                         let uu____12279 =
                                           let uu____12284 =
                                             let uu____12285 =
                                               print_implicit q  in
                                             let uu____12286 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12285 uu____12286
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12284)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12279
                                       else ());
                                      (let uu____12288 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12288, q)))) args wp_args
                           in
                        (head1, uu____12174)  in
                      FStar_Syntax_Syntax.Tm_app uu____12157  in
                    mk1 uu____12156)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12334 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12334 with
              | (binders_orig,comp1) ->
                  let uu____12341 =
                    let uu____12358 =
                      FStar_List.map
                        (fun uu____12398  ->
                           match uu____12398 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12426 = is_C h  in
                               if uu____12426
                               then
                                 let w' =
                                   let uu____12440 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12440
                                    in
                                 let uu____12441 =
                                   let uu____12450 =
                                     let uu____12459 =
                                       let uu____12466 =
                                         let uu____12467 =
                                           let uu____12468 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12468  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12467
                                          in
                                       (uu____12466, q)  in
                                     [uu____12459]  in
                                   (w', q) :: uu____12450  in
                                 (w', uu____12441)
                               else
                                 (let x =
                                    let uu____12501 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____12501
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12358  in
                  (match uu____12341 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____12574 =
                           let uu____12577 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12577
                            in
                         FStar_Syntax_Subst.subst_comp uu____12574 comp1  in
                       let app =
                         let uu____12581 =
                           let uu____12582 =
                             let uu____12599 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____12618 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____12619 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12618, uu____12619)) bvs
                                in
                             (wp, uu____12599)  in
                           FStar_Syntax_Syntax.Tm_app uu____12582  in
                         mk1 uu____12581  in
                       let comp3 =
                         let uu____12633 = type_of_comp comp2  in
                         let uu____12634 = is_monadic_comp comp2  in
                         trans_G env uu____12633 uu____12634 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____12636,uu____12637) ->
             trans_F_ env e wp
         | uu____12678 -> failwith "impossible trans_F_")

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
            let uu____12683 =
              let uu____12684 = star_type' env h  in
              let uu____12687 =
                let uu____12698 =
                  let uu____12707 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____12707)  in
                [uu____12698]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____12684;
                FStar_Syntax_Syntax.effect_args = uu____12687;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____12683
          else
            (let uu____12731 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____12731)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.delta_constant;
    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____12750 = n env.env t  in star_type' env uu____12750
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____12769 = n env.env t  in check_n env uu____12769
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____12785 = n env.env c  in
        let uu____12786 = n env.env wp  in
        trans_F_ env uu____12785 uu____12786
  