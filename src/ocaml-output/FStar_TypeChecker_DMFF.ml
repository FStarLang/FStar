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
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___353_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___353_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___353_123.FStar_Syntax_Syntax.index);
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
                  (fun uu____442  ->
                     match uu____442 with
                     | (t,b) ->
                         let uu____453 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____453))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____492 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____492))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____525 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____525)
                 in
              let uu____528 =
                let uu____545 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____569 =
                        let uu____572 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____572  in
                      FStar_Syntax_Util.arrow gamma uu____569  in
                    let uu____573 =
                      let uu____574 =
                        let uu____583 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____590 =
                          let uu____599 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____599]  in
                        uu____583 :: uu____590  in
                      FStar_List.append binders uu____574  in
                    FStar_Syntax_Util.abs uu____573 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____630 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____631 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____630, uu____631)  in
                match uu____545 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____671 =
                        let uu____672 =
                          let uu____689 =
                            let uu____700 =
                              FStar_List.map
                                (fun uu____722  ->
                                   match uu____722 with
                                   | (bv,uu____734) ->
                                       let uu____739 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____740 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____739, uu____740)) binders
                               in
                            let uu____741 =
                              let uu____748 =
                                let uu____753 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____754 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____753, uu____754)  in
                              let uu____755 =
                                let uu____762 =
                                  let uu____767 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____767)  in
                                [uu____762]  in
                              uu____748 :: uu____755  in
                            FStar_List.append uu____700 uu____741  in
                          (fv, uu____689)  in
                        FStar_Syntax_Syntax.Tm_app uu____672  in
                      mk1 uu____671  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____528 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____838 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____838
                       in
                    let ret1 =
                      let uu____842 =
                        let uu____843 =
                          let uu____846 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____846  in
                        FStar_Syntax_Util.residual_tot uu____843  in
                      FStar_Pervasives_Native.Some uu____842  in
                    let body =
                      let uu____850 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____850 ret1  in
                    let uu____853 =
                      let uu____854 = mk_all_implicit binders  in
                      let uu____861 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____854 uu____861  in
                    FStar_Syntax_Util.abs uu____853 body ret1  in
                  let c_pure1 =
                    let uu____889 = mk_lid "pure"  in
                    register env1 uu____889 c_pure  in
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
                      let uu____896 =
                        let uu____897 =
                          let uu____898 =
                            let uu____907 =
                              let uu____914 =
                                let uu____915 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____915
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____914  in
                            [uu____907]  in
                          let uu____928 =
                            let uu____931 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____931  in
                          FStar_Syntax_Util.arrow uu____898 uu____928  in
                        mk_gctx uu____897  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____896
                       in
                    let r =
                      let uu____933 =
                        let uu____934 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____934  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____933
                       in
                    let ret1 =
                      let uu____938 =
                        let uu____939 =
                          let uu____942 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____942  in
                        FStar_Syntax_Util.residual_tot uu____939  in
                      FStar_Pervasives_Native.Some uu____938  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____952 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____955 =
                          let uu____966 =
                            let uu____969 =
                              let uu____970 =
                                let uu____971 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____971
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____970  in
                            [uu____969]  in
                          FStar_List.append gamma_as_args uu____966  in
                        FStar_Syntax_Util.mk_app uu____952 uu____955  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____974 =
                      let uu____975 = mk_all_implicit binders  in
                      let uu____982 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____975 uu____982  in
                    FStar_Syntax_Util.abs uu____974 outer_body ret1  in
                  let c_app1 =
                    let uu____1018 = mk_lid "app"  in
                    register env1 uu____1018 c_app  in
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
                      let uu____1027 =
                        let uu____1036 =
                          let uu____1043 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1043  in
                        [uu____1036]  in
                      let uu____1056 =
                        let uu____1059 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1059  in
                      FStar_Syntax_Util.arrow uu____1027 uu____1056  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1062 =
                        let uu____1063 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1063  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1062
                       in
                    let ret1 =
                      let uu____1067 =
                        let uu____1068 =
                          let uu____1071 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1071  in
                        FStar_Syntax_Util.residual_tot uu____1068  in
                      FStar_Pervasives_Native.Some uu____1067  in
                    let uu____1072 =
                      let uu____1073 = mk_all_implicit binders  in
                      let uu____1080 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____1073 uu____1080  in
                    let uu____1115 =
                      let uu____1118 =
                        let uu____1129 =
                          let uu____1132 =
                            let uu____1133 =
                              let uu____1144 =
                                let uu____1147 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1147]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1144
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1133  in
                          let uu____1156 =
                            let uu____1159 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1159]  in
                          uu____1132 :: uu____1156  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1129
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1118  in
                    FStar_Syntax_Util.abs uu____1072 uu____1115 ret1  in
                  let c_lift11 =
                    let uu____1169 = mk_lid "lift1"  in
                    register env1 uu____1169 c_lift1  in
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
                      let uu____1179 =
                        let uu____1188 =
                          let uu____1195 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1195  in
                        let uu____1196 =
                          let uu____1205 =
                            let uu____1212 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1212  in
                          [uu____1205]  in
                        uu____1188 :: uu____1196  in
                      let uu____1231 =
                        let uu____1234 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1234  in
                      FStar_Syntax_Util.arrow uu____1179 uu____1231  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1237 =
                        let uu____1238 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1238  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1237
                       in
                    let a2 =
                      let uu____1240 =
                        let uu____1241 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1241  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1240
                       in
                    let ret1 =
                      let uu____1245 =
                        let uu____1246 =
                          let uu____1249 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1249  in
                        FStar_Syntax_Util.residual_tot uu____1246  in
                      FStar_Pervasives_Native.Some uu____1245  in
                    let uu____1250 =
                      let uu____1251 = mk_all_implicit binders  in
                      let uu____1258 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1251 uu____1258  in
                    let uu____1301 =
                      let uu____1304 =
                        let uu____1315 =
                          let uu____1318 =
                            let uu____1319 =
                              let uu____1330 =
                                let uu____1333 =
                                  let uu____1334 =
                                    let uu____1345 =
                                      let uu____1348 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1348]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1345
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1334
                                   in
                                let uu____1357 =
                                  let uu____1360 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1360]  in
                                uu____1333 :: uu____1357  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1330
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1319  in
                          let uu____1369 =
                            let uu____1372 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1372]  in
                          uu____1318 :: uu____1369  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1315
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1304  in
                    FStar_Syntax_Util.abs uu____1250 uu____1301 ret1  in
                  let c_lift21 =
                    let uu____1382 = mk_lid "lift2"  in
                    register env1 uu____1382 c_lift2  in
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
                      let uu____1391 =
                        let uu____1400 =
                          let uu____1407 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1407  in
                        [uu____1400]  in
                      let uu____1420 =
                        let uu____1423 =
                          let uu____1424 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1424  in
                        FStar_Syntax_Syntax.mk_Total uu____1423  in
                      FStar_Syntax_Util.arrow uu____1391 uu____1420  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1429 =
                        let uu____1430 =
                          let uu____1433 =
                            let uu____1434 =
                              let uu____1443 =
                                let uu____1450 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1450
                                 in
                              [uu____1443]  in
                            let uu____1463 =
                              let uu____1466 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1466  in
                            FStar_Syntax_Util.arrow uu____1434 uu____1463  in
                          mk_ctx uu____1433  in
                        FStar_Syntax_Util.residual_tot uu____1430  in
                      FStar_Pervasives_Native.Some uu____1429  in
                    let e1 =
                      let uu____1468 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1468
                       in
                    let body =
                      let uu____1472 =
                        let uu____1473 =
                          let uu____1482 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1482]  in
                        FStar_List.append gamma uu____1473  in
                      let uu____1507 =
                        let uu____1510 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1513 =
                          let uu____1524 =
                            let uu____1525 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1525  in
                          let uu____1526 = args_of_binders1 gamma  in
                          uu____1524 :: uu____1526  in
                        FStar_Syntax_Util.mk_app uu____1510 uu____1513  in
                      FStar_Syntax_Util.abs uu____1472 uu____1507 ret1  in
                    let uu____1529 =
                      let uu____1530 = mk_all_implicit binders  in
                      let uu____1537 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1530 uu____1537  in
                    FStar_Syntax_Util.abs uu____1529 body ret1  in
                  let c_push1 =
                    let uu____1569 = mk_lid "push"  in
                    register env1 uu____1569 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1593 =
                        let uu____1594 =
                          let uu____1611 = args_of_binders1 binders  in
                          (c, uu____1611)  in
                        FStar_Syntax_Syntax.Tm_app uu____1594  in
                      mk1 uu____1593
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1639 =
                        let uu____1640 =
                          let uu____1649 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1656 =
                            let uu____1665 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1665]  in
                          uu____1649 :: uu____1656  in
                        let uu____1690 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1640 uu____1690  in
                      FStar_Syntax_Syntax.mk_Total uu____1639  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1694 =
                      let uu____1695 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1695  in
                    let uu____1710 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1714 =
                        let uu____1717 =
                          let uu____1728 =
                            let uu____1731 =
                              let uu____1732 =
                                let uu____1743 =
                                  let uu____1752 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1752  in
                                [uu____1743]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1732  in
                            [uu____1731]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1728
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1717  in
                      FStar_Syntax_Util.ascribe uu____1714
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1694 uu____1710
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1796 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1796 wp_if_then_else  in
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
                      let uu____1809 =
                        let uu____1820 =
                          let uu____1823 =
                            let uu____1824 =
                              let uu____1835 =
                                let uu____1838 =
                                  let uu____1839 =
                                    let uu____1850 =
                                      let uu____1859 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1859
                                       in
                                    [uu____1850]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1839
                                   in
                                [uu____1838]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1835
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1824  in
                          let uu____1884 =
                            let uu____1887 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1887]  in
                          uu____1823 :: uu____1884  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1820
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1809  in
                    let uu____1896 =
                      let uu____1897 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1897  in
                    FStar_Syntax_Util.abs uu____1896 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1913 = mk_lid "wp_assert"  in
                    register env1 uu____1913 wp_assert  in
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
                      let uu____1926 =
                        let uu____1937 =
                          let uu____1940 =
                            let uu____1941 =
                              let uu____1952 =
                                let uu____1955 =
                                  let uu____1956 =
                                    let uu____1967 =
                                      let uu____1976 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1976
                                       in
                                    [uu____1967]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1956
                                   in
                                [uu____1955]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1952
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1941  in
                          let uu____2001 =
                            let uu____2004 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2004]  in
                          uu____1940 :: uu____2001  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1937
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1926  in
                    let uu____2013 =
                      let uu____2014 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____2014  in
                    FStar_Syntax_Util.abs uu____2013 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____2030 = mk_lid "wp_assume"  in
                    register env1 uu____2030 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____2041 =
                        let uu____2050 =
                          let uu____2057 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____2057  in
                        [uu____2050]  in
                      let uu____2070 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____2041 uu____2070  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____2077 =
                        let uu____2088 =
                          let uu____2091 =
                            let uu____2092 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____2092  in
                          let uu____2111 =
                            let uu____2114 =
                              let uu____2115 =
                                let uu____2126 =
                                  let uu____2129 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____2129]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____2126
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____2115  in
                            [uu____2114]  in
                          uu____2091 :: uu____2111  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2088
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____2077  in
                    let uu____2146 =
                      let uu____2147 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____2147  in
                    FStar_Syntax_Util.abs uu____2146 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____2163 = mk_lid "wp_close"  in
                    register env1 uu____2163 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____2173 =
                      let uu____2174 =
                        let uu____2175 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2175
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____2174  in
                    FStar_Pervasives_Native.Some uu____2173  in
                  let mk_forall1 x body =
                    let uu____2187 =
                      let uu____2194 =
                        let uu____2195 =
                          let uu____2212 =
                            let uu____2223 =
                              let uu____2232 =
                                let uu____2233 =
                                  let uu____2234 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____2234]  in
                                FStar_Syntax_Util.abs uu____2233 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____2232  in
                            [uu____2223]  in
                          (FStar_Syntax_Util.tforall, uu____2212)  in
                        FStar_Syntax_Syntax.Tm_app uu____2195  in
                      FStar_Syntax_Syntax.mk uu____2194  in
                    uu____2187 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2294 =
                      let uu____2295 = FStar_Syntax_Subst.compress t  in
                      uu____2295.FStar_Syntax_Syntax.n  in
                    match uu____2294 with
                    | FStar_Syntax_Syntax.Tm_type uu____2298 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2330  ->
                              match uu____2330 with
                              | (b,uu____2338) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2343 -> true  in
                  let rec is_monotonic t =
                    let uu____2354 =
                      let uu____2355 = FStar_Syntax_Subst.compress t  in
                      uu____2355.FStar_Syntax_Syntax.n  in
                    match uu____2354 with
                    | FStar_Syntax_Syntax.Tm_type uu____2358 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2390  ->
                              match uu____2390 with
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
                            let uu____2539 =
                              let uu____2542 =
                                let uu____2553 =
                                  let uu____2562 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2562  in
                                [uu____2553]  in
                              FStar_Syntax_Util.mk_app x uu____2542  in
                            let uu____2579 =
                              let uu____2582 =
                                let uu____2593 =
                                  let uu____2602 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2602  in
                                [uu____2593]  in
                              FStar_Syntax_Util.mk_app y uu____2582  in
                            mk_rel1 b uu____2539 uu____2579  in
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
                             let uu____2623 =
                               let uu____2626 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2629 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2626 uu____2629  in
                             let uu____2632 =
                               let uu____2635 =
                                 let uu____2638 =
                                   let uu____2649 =
                                     let uu____2658 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2658
                                      in
                                   [uu____2649]  in
                                 FStar_Syntax_Util.mk_app x uu____2638  in
                               let uu____2675 =
                                 let uu____2678 =
                                   let uu____2689 =
                                     let uu____2698 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2698
                                      in
                                   [uu____2689]  in
                                 FStar_Syntax_Util.mk_app y uu____2678  in
                               mk_rel1 b uu____2635 uu____2675  in
                             FStar_Syntax_Util.mk_imp uu____2623 uu____2632
                              in
                           let uu____2715 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2715)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2718);
                                      FStar_Syntax_Syntax.pos = uu____2719;
                                      FStar_Syntax_Syntax.vars = uu____2720;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2764 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2764
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2771 =
                              let uu____2774 =
                                let uu____2785 =
                                  let uu____2794 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2794  in
                                [uu____2785]  in
                              FStar_Syntax_Util.mk_app x uu____2774  in
                            let uu____2811 =
                              let uu____2814 =
                                let uu____2825 =
                                  let uu____2834 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2834  in
                                [uu____2825]  in
                              FStar_Syntax_Util.mk_app y uu____2814  in
                            mk_rel1 b uu____2771 uu____2811  in
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
                             let uu____2855 =
                               let uu____2858 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2861 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2858 uu____2861  in
                             let uu____2864 =
                               let uu____2867 =
                                 let uu____2870 =
                                   let uu____2881 =
                                     let uu____2890 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2890
                                      in
                                   [uu____2881]  in
                                 FStar_Syntax_Util.mk_app x uu____2870  in
                               let uu____2907 =
                                 let uu____2910 =
                                   let uu____2921 =
                                     let uu____2930 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2930
                                      in
                                   [uu____2921]  in
                                 FStar_Syntax_Util.mk_app y uu____2910  in
                               mk_rel1 b uu____2867 uu____2907  in
                             FStar_Syntax_Util.mk_imp uu____2855 uu____2864
                              in
                           let uu____2947 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2947)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___354_2986 = t1  in
                          let uu____2987 =
                            let uu____2988 =
                              let uu____3003 =
                                let uu____3006 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____3006  in
                              ([binder], uu____3003)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2988  in
                          {
                            FStar_Syntax_Syntax.n = uu____2987;
                            FStar_Syntax_Syntax.pos =
                              (uu___354_2986.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___354_2986.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____3029 ->
                        failwith "unhandled arrow"
                    | uu____3046 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____3081 =
                        let uu____3082 = FStar_Syntax_Subst.compress t1  in
                        uu____3082.FStar_Syntax_Syntax.n  in
                      match uu____3081 with
                      | FStar_Syntax_Syntax.Tm_type uu____3085 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____3112 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____3112
                          ->
                          let project i tuple =
                            let projector =
                              let uu____3131 =
                                let uu____3132 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____3132 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____3131
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____3161 =
                            let uu____3172 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____3190  ->
                                     match uu____3190 with
                                     | (t2,q) ->
                                         let uu____3209 = project i x  in
                                         let uu____3212 = project i y  in
                                         mk_stronger t2 uu____3209 uu____3212)
                                args
                               in
                            match uu____3172 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____3161 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____3265);
                                      FStar_Syntax_Syntax.pos = uu____3266;
                                      FStar_Syntax_Syntax.vars = uu____3267;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3311  ->
                                   match uu____3311 with
                                   | (bv,q) ->
                                       let uu____3324 =
                                         let uu____3325 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3325  in
                                       FStar_Syntax_Syntax.gen_bv uu____3324
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3332 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3332) bvs
                             in
                          let body =
                            let uu____3334 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3337 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3334 uu____3337  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____3346);
                                      FStar_Syntax_Syntax.pos = uu____3347;
                                      FStar_Syntax_Syntax.vars = uu____3348;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____3392  ->
                                   match uu____3392 with
                                   | (bv,q) ->
                                       let uu____3405 =
                                         let uu____3406 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____3406  in
                                       FStar_Syntax_Syntax.gen_bv uu____3405
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3413 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3413) bvs
                             in
                          let body =
                            let uu____3415 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3418 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3415 uu____3418  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3425 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3427 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3430 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3433 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3427 uu____3430 uu____3433  in
                    let uu____3436 =
                      let uu____3437 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3437  in
                    FStar_Syntax_Util.abs uu____3436 body ret_tot_type  in
                  let stronger1 =
                    let uu____3469 = mk_lid "stronger"  in
                    register env1 uu____3469 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3475 = FStar_Util.prefix gamma  in
                    match uu____3475 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3540 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3540
                             in
                          let uu____3545 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3545 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3555 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3555  in
                              let guard_free1 =
                                let uu____3567 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3567  in
                              let pat =
                                let uu____3571 =
                                  let uu____3582 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3582]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3571
                                 in
                              let pattern_guarded_body =
                                let uu____3610 =
                                  let uu____3611 =
                                    let uu____3618 =
                                      let uu____3619 =
                                        let uu____3632 =
                                          let uu____3643 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3643]  in
                                        [uu____3632]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3619
                                       in
                                    (body, uu____3618)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3611  in
                                mk1 uu____3610  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3690 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3698 =
                            let uu____3701 =
                              let uu____3702 =
                                let uu____3705 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3708 =
                                  let uu____3719 = args_of_binders1 wp_args
                                     in
                                  let uu____3722 =
                                    let uu____3725 =
                                      let uu____3726 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3726
                                       in
                                    [uu____3725]  in
                                  FStar_List.append uu____3719 uu____3722  in
                                FStar_Syntax_Util.mk_app uu____3705
                                  uu____3708
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3702  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3701
                             in
                          FStar_Syntax_Util.abs gamma uu____3698
                            ret_gtot_type
                           in
                        let uu____3727 =
                          let uu____3728 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3728  in
                        FStar_Syntax_Util.abs uu____3727 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3744 = mk_lid "wp_ite"  in
                    register env1 uu____3744 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3750 = FStar_Util.prefix gamma  in
                    match uu____3750 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3807 =
                            let uu____3808 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3815 =
                              let uu____3826 =
                                let uu____3835 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3835  in
                              [uu____3826]  in
                            FStar_Syntax_Util.mk_app uu____3808 uu____3815
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3807
                           in
                        let uu____3852 =
                          let uu____3853 =
                            let uu____3862 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3862 gamma  in
                          FStar_List.append binders uu____3853  in
                        FStar_Syntax_Util.abs uu____3852 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3884 = mk_lid "null_wp"  in
                    register env1 uu____3884 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3895 =
                        let uu____3906 =
                          let uu____3909 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3910 =
                            let uu____3913 =
                              let uu____3914 =
                                let uu____3925 =
                                  let uu____3934 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3934  in
                                [uu____3925]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3914
                               in
                            let uu____3951 =
                              let uu____3954 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3954]  in
                            uu____3913 :: uu____3951  in
                          uu____3909 :: uu____3910  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3906
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3895  in
                    let uu____3963 =
                      let uu____3964 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3964  in
                    FStar_Syntax_Util.abs uu____3963 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3980 = mk_lid "wp_trivial"  in
                    register env1 uu____3980 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3985 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3985
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____3992 =
                      let uu____3993 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____3993  in
                    let uu____4041 =
                      let uu___355_4042 = ed  in
                      let uu____4043 =
                        let uu____4044 = c wp_if_then_else2  in
                        ([], uu____4044)  in
                      let uu____4051 =
                        let uu____4052 = c wp_ite2  in ([], uu____4052)  in
                      let uu____4059 =
                        let uu____4060 = c stronger2  in ([], uu____4060)  in
                      let uu____4067 =
                        let uu____4068 = c wp_close2  in ([], uu____4068)  in
                      let uu____4075 =
                        let uu____4076 = c wp_assert2  in ([], uu____4076)
                         in
                      let uu____4083 =
                        let uu____4084 = c wp_assume2  in ([], uu____4084)
                         in
                      let uu____4091 =
                        let uu____4092 = c null_wp2  in ([], uu____4092)  in
                      let uu____4099 =
                        let uu____4100 = c wp_trivial2  in ([], uu____4100)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___355_4042.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___355_4042.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___355_4042.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___355_4042.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___355_4042.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___355_4042.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___355_4042.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____4043;
                        FStar_Syntax_Syntax.ite_wp = uu____4051;
                        FStar_Syntax_Syntax.stronger = uu____4059;
                        FStar_Syntax_Syntax.close_wp = uu____4067;
                        FStar_Syntax_Syntax.assert_p = uu____4075;
                        FStar_Syntax_Syntax.assume_p = uu____4083;
                        FStar_Syntax_Syntax.null_wp = uu____4091;
                        FStar_Syntax_Syntax.trivial = uu____4099;
                        FStar_Syntax_Syntax.repr =
                          (uu___355_4042.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___355_4042.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___355_4042.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___355_4042.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___355_4042.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____3992, uu____4041)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___356_4122 = dmff_env  in
      {
        env = env';
        subst = (uu___356_4122.subst);
        tc_const = (uu___356_4122.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____4139 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____4153 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___342_4165  ->
    match uu___342_4165 with
    | FStar_Syntax_Syntax.Total (t,uu____4167) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___341_4180  ->
                match uu___341_4180 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4181 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____4183 =
          let uu____4184 =
            let uu____4185 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____4185
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____4184  in
        failwith uu____4183
    | FStar_Syntax_Syntax.GTotal uu____4186 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___343_4199  ->
    match uu___343_4199 with
    | N t ->
        let uu____4201 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____4201
    | M t ->
        let uu____4203 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____4203
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____4209,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____4211;
                      FStar_Syntax_Syntax.vars = uu____4212;_})
        -> nm_of_comp n2
    | uu____4233 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____4243 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____4243 with | M uu____4244 -> true | N uu____4245 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____4251 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____4265 =
        let uu____4274 =
          let uu____4281 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4281  in
        [uu____4274]  in
      let uu____4300 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____4265 uu____4300  in
    let uu____4303 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____4303
  
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
        let uu____4344 =
          let uu____4345 =
            let uu____4360 =
              let uu____4369 =
                let uu____4376 =
                  let uu____4377 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____4377  in
                let uu____4378 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____4376, uu____4378)  in
              [uu____4369]  in
            let uu____4395 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____4360, uu____4395)  in
          FStar_Syntax_Syntax.Tm_arrow uu____4345  in
        mk1 uu____4344

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
                       let uu___357_4501 = bv  in
                       let uu____4502 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___357_4501.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___357_4501.FStar_Syntax_Syntax.index);
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
                        let uu____4670 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4620, uu____4670)  in
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
                   (let uu____4758 = f x  in
                    FStar_Util.string_builder_append strb uu____4758);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4765 = f x1  in
                         FStar_Util.string_builder_append strb uu____4765))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4767 =
              let uu____4772 =
                let uu____4773 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4774 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4773 uu____4774
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4772)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4767  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4790 =
              let uu____4791 = FStar_Syntax_Subst.compress ty  in
              uu____4791.FStar_Syntax_Syntax.n  in
            match uu____4790 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4816 =
                  let uu____4817 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4817  in
                if uu____4816
                then false
                else
                  (try
                     (fun uu___359_4828  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4851 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4851 s  in
                              let uu____4854 =
                                let uu____4855 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4855  in
                              if uu____4854
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4858 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4858 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4882  ->
                                          match uu____4882 with
                                          | (bv,uu____4894) ->
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
            | uu____4914 ->
                ((let uu____4916 =
                    let uu____4921 =
                      let uu____4922 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4922
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4921)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4916);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4933 =
              let uu____4934 = FStar_Syntax_Subst.compress head2  in
              uu____4934.FStar_Syntax_Syntax.n  in
            match uu____4933 with
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
                  (let uu____4939 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4939)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4941 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4941 with
                 | ((uu____4950,ty),uu____4952) ->
                     let uu____4957 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4957
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.env t1
                          in
                       let uu____4967 =
                         let uu____4968 = FStar_Syntax_Subst.compress res  in
                         uu____4968.FStar_Syntax_Syntax.n  in
                       (match uu____4967 with
                        | FStar_Syntax_Syntax.Tm_app uu____4971 -> true
                        | uu____4988 ->
                            ((let uu____4990 =
                                let uu____4995 =
                                  let uu____4996 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____4996
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____4995)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____4990);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____4998 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4999 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5001) ->
                is_valid_application t2
            | uu____5006 -> false  in
          let uu____5007 = is_valid_application head1  in
          if uu____5007
          then
            let uu____5008 =
              let uu____5009 =
                let uu____5026 =
                  FStar_List.map
                    (fun uu____5055  ->
                       match uu____5055 with
                       | (t2,qual) ->
                           let uu____5080 = star_type' env t2  in
                           (uu____5080, qual)) args
                   in
                (head1, uu____5026)  in
              FStar_Syntax_Syntax.Tm_app uu____5009  in
            mk1 uu____5008
          else
            (let uu____5096 =
               let uu____5101 =
                 let uu____5102 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____5102
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____5101)  in
             FStar_Errors.raise_err uu____5096)
      | FStar_Syntax_Syntax.Tm_bvar uu____5103 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____5104 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____5105 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____5106 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____5134 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____5134 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___360_5142 = env  in
                 let uu____5143 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____5143;
                   subst = (uu___360_5142.subst);
                   tc_const = (uu___360_5142.tc_const)
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
               ((let uu___361_5165 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___361_5165.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___361_5165.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____5172 =
            let uu____5173 =
              let uu____5180 = star_type' env t2  in (uu____5180, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____5173  in
          mk1 uu____5172
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____5232 =
            let uu____5233 =
              let uu____5260 = star_type' env e  in
              let uu____5263 =
                let uu____5280 =
                  let uu____5289 = star_type' env t2  in
                  FStar_Util.Inl uu____5289  in
                (uu____5280, FStar_Pervasives_Native.None)  in
              (uu____5260, uu____5263, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5233  in
          mk1 uu____5232
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____5377 =
            let uu____5378 =
              let uu____5405 = star_type' env e  in
              let uu____5408 =
                let uu____5425 =
                  let uu____5434 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____5434  in
                (uu____5425, FStar_Pervasives_Native.None)  in
              (uu____5405, uu____5408, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____5378  in
          mk1 uu____5377
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5475,(uu____5476,FStar_Pervasives_Native.Some uu____5477),uu____5478)
          ->
          let uu____5527 =
            let uu____5532 =
              let uu____5533 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5533
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5532)  in
          FStar_Errors.raise_err uu____5527
      | FStar_Syntax_Syntax.Tm_refine uu____5534 ->
          let uu____5541 =
            let uu____5546 =
              let uu____5547 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5547
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5546)  in
          FStar_Errors.raise_err uu____5541
      | FStar_Syntax_Syntax.Tm_uinst uu____5548 ->
          let uu____5555 =
            let uu____5560 =
              let uu____5561 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5561
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5560)  in
          FStar_Errors.raise_err uu____5555
      | FStar_Syntax_Syntax.Tm_quoted uu____5562 ->
          let uu____5569 =
            let uu____5574 =
              let uu____5575 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5575
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5574)  in
          FStar_Errors.raise_err uu____5569
      | FStar_Syntax_Syntax.Tm_constant uu____5576 ->
          let uu____5577 =
            let uu____5582 =
              let uu____5583 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5583
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5582)  in
          FStar_Errors.raise_err uu____5577
      | FStar_Syntax_Syntax.Tm_match uu____5584 ->
          let uu____5607 =
            let uu____5612 =
              let uu____5613 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5613
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5612)  in
          FStar_Errors.raise_err uu____5607
      | FStar_Syntax_Syntax.Tm_let uu____5614 ->
          let uu____5627 =
            let uu____5632 =
              let uu____5633 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5633
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5632)  in
          FStar_Errors.raise_err uu____5627
      | FStar_Syntax_Syntax.Tm_uvar uu____5634 ->
          let uu____5647 =
            let uu____5652 =
              let uu____5653 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5653
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5652)  in
          FStar_Errors.raise_err uu____5647
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5654 =
            let uu____5659 =
              let uu____5660 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5660
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5659)  in
          FStar_Errors.raise_err uu____5654
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5662 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5662
      | FStar_Syntax_Syntax.Tm_delayed uu____5665 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___345_5694  ->
    match uu___345_5694 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___344_5701  ->
                match uu___344_5701 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5702 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5708 =
      let uu____5709 = FStar_Syntax_Subst.compress t  in
      uu____5709.FStar_Syntax_Syntax.n  in
    match uu____5708 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5739 =
            let uu____5740 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5740  in
          is_C uu____5739  in
        if r
        then
          ((let uu____5762 =
              let uu____5763 =
                FStar_List.for_all
                  (fun uu____5773  ->
                     match uu____5773 with | (h,uu____5781) -> is_C h) args
                 in
              Prims.op_Negation uu____5763  in
            if uu____5762 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5789 =
              let uu____5790 =
                FStar_List.for_all
                  (fun uu____5801  ->
                     match uu____5801 with
                     | (h,uu____5809) ->
                         let uu____5814 = is_C h  in
                         Prims.op_Negation uu____5814) args
                 in
              Prims.op_Negation uu____5790  in
            if uu____5789 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5838 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5838 with
         | M t1 ->
             ((let uu____5841 = is_C t1  in
               if uu____5841 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5845) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5851) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5857,uu____5858) -> is_C t1
    | uu____5899 -> false
  
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
          let uu____5932 =
            let uu____5933 =
              let uu____5950 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____5953 =
                let uu____5964 =
                  let uu____5973 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____5973)  in
                [uu____5964]  in
              (uu____5950, uu____5953)  in
            FStar_Syntax_Syntax.Tm_app uu____5933  in
          mk1 uu____5932  in
        let uu____6008 =
          let uu____6009 = FStar_Syntax_Syntax.mk_binder p  in [uu____6009]
           in
        FStar_Syntax_Util.abs uu____6008 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___346_6032  ->
    match uu___346_6032 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6033 -> false
  
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
        let return_if uu____6268 =
          match uu____6268 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____6305 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6307 =
                       let uu____6308 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____6308  in
                     Prims.op_Negation uu____6307)
                   in
                if uu____6305
                then
                  let uu____6309 =
                    let uu____6314 =
                      let uu____6315 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____6316 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____6317 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6315 uu____6316 uu____6317
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6314)  in
                  FStar_Errors.raise_err uu____6309
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____6338 = mk_return env t1 s_e  in
                     ((M t1), uu____6338, u_e)))
               | (M t1,N t2) ->
                   let uu____6345 =
                     let uu____6350 =
                       let uu____6351 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____6352 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____6353 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6351 uu____6352 uu____6353
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6350)
                      in
                   FStar_Errors.raise_err uu____6345)
           in
        let ensure_m env1 e2 =
          let strip_m uu___347_6402 =
            match uu___347_6402 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____6418 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____6438 =
                let uu____6443 =
                  let uu____6444 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6444
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6443)  in
              FStar_Errors.raise_error uu____6438 e2.FStar_Syntax_Syntax.pos
          | M uu____6451 ->
              let uu____6452 = check env1 e2 context_nm  in
              strip_m uu____6452
           in
        let uu____6459 =
          let uu____6460 = FStar_Syntax_Subst.compress e  in
          uu____6460.FStar_Syntax_Syntax.n  in
        match uu____6459 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6469 ->
            let uu____6470 = infer env e  in return_if uu____6470
        | FStar_Syntax_Syntax.Tm_name uu____6477 ->
            let uu____6478 = infer env e  in return_if uu____6478
        | FStar_Syntax_Syntax.Tm_fvar uu____6485 ->
            let uu____6486 = infer env e  in return_if uu____6486
        | FStar_Syntax_Syntax.Tm_abs uu____6493 ->
            let uu____6512 = infer env e  in return_if uu____6512
        | FStar_Syntax_Syntax.Tm_constant uu____6519 ->
            let uu____6520 = infer env e  in return_if uu____6520
        | FStar_Syntax_Syntax.Tm_quoted uu____6527 ->
            let uu____6534 = infer env e  in return_if uu____6534
        | FStar_Syntax_Syntax.Tm_app uu____6541 ->
            let uu____6558 = infer env e  in return_if uu____6558
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6566 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____6566 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____6628) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6634) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6640,uu____6641) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6682 ->
            let uu____6695 =
              let uu____6696 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6696  in
            failwith uu____6695
        | FStar_Syntax_Syntax.Tm_type uu____6703 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6710 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6731 ->
            let uu____6738 =
              let uu____6739 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6739  in
            failwith uu____6738
        | FStar_Syntax_Syntax.Tm_uvar uu____6746 ->
            let uu____6759 =
              let uu____6760 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6760  in
            failwith uu____6759
        | FStar_Syntax_Syntax.Tm_delayed uu____6767 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6796 =
              let uu____6797 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6797  in
            failwith uu____6796

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
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env.env
         in
      let uu____6825 =
        let uu____6826 = FStar_Syntax_Subst.compress e  in
        uu____6826.FStar_Syntax_Syntax.n  in
      match uu____6825 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6844 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6844
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6895;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____6896;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6902 =
                  let uu___362_6903 = rc  in
                  let uu____6904 =
                    let uu____6909 =
                      let uu____6912 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____6912  in
                    FStar_Pervasives_Native.Some uu____6909  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___362_6903.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6904;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___362_6903.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____6902
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___363_6924 = env  in
            let uu____6925 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____6925;
              subst = (uu___363_6924.subst);
              tc_const = (uu___363_6924.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____6951  ->
                 match uu____6951 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___364_6974 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___364_6974.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___364_6974.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____6975 =
            FStar_List.fold_left
              (fun uu____7006  ->
                 fun uu____7007  ->
                   match (uu____7006, uu____7007) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____7065 = is_C c  in
                       if uu____7065
                       then
                         let xw =
                           let uu____7073 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____7073
                            in
                         let x =
                           let uu___365_7075 = bv  in
                           let uu____7076 =
                             let uu____7079 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____7079  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___365_7075.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___365_7075.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____7076
                           }  in
                         let env3 =
                           let uu___366_7081 = env2  in
                           let uu____7082 =
                             let uu____7085 =
                               let uu____7086 =
                                 let uu____7093 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____7093)  in
                               FStar_Syntax_Syntax.NT uu____7086  in
                             uu____7085 :: (env2.subst)  in
                           {
                             env = (uu___366_7081.env);
                             subst = uu____7082;
                             tc_const = (uu___366_7081.tc_const)
                           }  in
                         let uu____7098 =
                           let uu____7101 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____7102 =
                             let uu____7105 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____7105 :: acc  in
                           uu____7101 :: uu____7102  in
                         (env3, uu____7098)
                       else
                         (let x =
                            let uu___367_7110 = bv  in
                            let uu____7111 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___367_7110.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___367_7110.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____7111
                            }  in
                          let uu____7114 =
                            let uu____7117 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____7117 :: acc  in
                          (env2, uu____7114))) (env1, []) binders1
             in
          (match uu____6975 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____7137 =
                 let check_what =
                   let uu____7163 = is_monadic rc_opt1  in
                   if uu____7163 then check_m else check_n  in
                 let uu____7177 = check_what env2 body1  in
                 match uu____7177 with
                 | (t,s_body,u_body) ->
                     let uu____7197 =
                       let uu____7200 =
                         let uu____7201 = is_monadic rc_opt1  in
                         if uu____7201 then M t else N t  in
                       comp_of_nm uu____7200  in
                     (uu____7197, s_body, u_body)
                  in
               (match uu____7137 with
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
                                 let uu____7238 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___348_7242  ->
                                           match uu___348_7242 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____7243 -> false))
                                    in
                                 if uu____7238
                                 then
                                   let uu____7244 =
                                     FStar_List.filter
                                       (fun uu___349_7248  ->
                                          match uu___349_7248 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____7249 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____7244
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____7258 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___350_7262  ->
                                         match uu___350_7262 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____7263 -> false))
                                  in
                               if uu____7258
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___351_7270  ->
                                        match uu___351_7270 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____7271 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____7272 =
                                   let uu____7273 =
                                     let uu____7278 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____7278
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____7273 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____7272
                               else
                                 (let uu____7284 =
                                    let uu___368_7285 = rc  in
                                    let uu____7286 =
                                      let uu____7291 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____7291
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___368_7285.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____7286;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___368_7285.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____7284))
                       in
                    let uu____7296 =
                      let comp1 =
                        let uu____7304 = is_monadic rc_opt1  in
                        let uu____7305 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____7304 uu____7305
                         in
                      let uu____7306 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____7306,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____7296 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____7344 =
                             let uu____7345 =
                               let uu____7364 =
                                 let uu____7367 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____7367 s_rc_opt  in
                               (s_binders1, s_body1, uu____7364)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7345  in
                           mk1 uu____7344  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____7387 =
                             let uu____7388 =
                               let uu____7407 =
                                 let uu____7410 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____7410 u_rc_opt  in
                               (u_binders2, u_body2, uu____7407)  in
                             FStar_Syntax_Syntax.Tm_abs uu____7388  in
                           mk1 uu____7387  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7426;_};
            FStar_Syntax_Syntax.fv_delta = uu____7427;
            FStar_Syntax_Syntax.fv_qual = uu____7428;_}
          ->
          let uu____7431 =
            let uu____7436 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7436  in
          (match uu____7431 with
           | (uu____7467,t) ->
               let uu____7469 =
                 let uu____7470 = normalize1 t  in N uu____7470  in
               (uu____7469, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7471;
             FStar_Syntax_Syntax.vars = uu____7472;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7551 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7551 with
           | (unary_op1,uu____7575) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7646;
             FStar_Syntax_Syntax.vars = uu____7647;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____7743 = FStar_Syntax_Util.head_and_args e  in
          (match uu____7743 with
           | (unary_op1,uu____7767) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7846;
             FStar_Syntax_Syntax.vars = uu____7847;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____7885 = infer env a  in
          (match uu____7885 with
           | (t,s,u) ->
               let uu____7901 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7901 with
                | (head1,uu____7925) ->
                    let uu____7950 =
                      let uu____7951 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____7951  in
                    let uu____7952 =
                      let uu____7953 =
                        let uu____7954 =
                          let uu____7971 =
                            let uu____7982 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7982]  in
                          (head1, uu____7971)  in
                        FStar_Syntax_Syntax.Tm_app uu____7954  in
                      mk1 uu____7953  in
                    let uu____8019 =
                      let uu____8020 =
                        let uu____8021 =
                          let uu____8038 =
                            let uu____8049 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8049]  in
                          (head1, uu____8038)  in
                        FStar_Syntax_Syntax.Tm_app uu____8021  in
                      mk1 uu____8020  in
                    (uu____7950, uu____7952, uu____8019)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8086;
             FStar_Syntax_Syntax.vars = uu____8087;_},(a1,uu____8089)::a2::[])
          ->
          let uu____8145 = infer env a1  in
          (match uu____8145 with
           | (t,s,u) ->
               let uu____8161 = FStar_Syntax_Util.head_and_args e  in
               (match uu____8161 with
                | (head1,uu____8185) ->
                    let uu____8210 =
                      let uu____8211 =
                        let uu____8212 =
                          let uu____8229 =
                            let uu____8240 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____8240; a2]  in
                          (head1, uu____8229)  in
                        FStar_Syntax_Syntax.Tm_app uu____8212  in
                      mk1 uu____8211  in
                    let uu____8285 =
                      let uu____8286 =
                        let uu____8287 =
                          let uu____8304 =
                            let uu____8315 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____8315; a2]  in
                          (head1, uu____8304)  in
                        FStar_Syntax_Syntax.Tm_app uu____8287  in
                      mk1 uu____8286  in
                    (t, uu____8210, uu____8285)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____8360;
             FStar_Syntax_Syntax.vars = uu____8361;_},uu____8362)
          ->
          let uu____8387 =
            let uu____8392 =
              let uu____8393 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8393
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8392)  in
          FStar_Errors.raise_error uu____8387 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____8400;
             FStar_Syntax_Syntax.vars = uu____8401;_},uu____8402)
          ->
          let uu____8427 =
            let uu____8432 =
              let uu____8433 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8433
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8432)  in
          FStar_Errors.raise_error uu____8427 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____8466 = check_n env head1  in
          (match uu____8466 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____8488 =
                   let uu____8489 = FStar_Syntax_Subst.compress t  in
                   uu____8489.FStar_Syntax_Syntax.n  in
                 match uu____8488 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8492 -> true
                 | uu____8507 -> false  in
               let rec flatten1 t =
                 let uu____8528 =
                   let uu____8529 = FStar_Syntax_Subst.compress t  in
                   uu____8529.FStar_Syntax_Syntax.n  in
                 match uu____8528 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____8548);
                                FStar_Syntax_Syntax.pos = uu____8549;
                                FStar_Syntax_Syntax.vars = uu____8550;_})
                     when is_arrow t1 ->
                     let uu____8579 = flatten1 t1  in
                     (match uu____8579 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8679,uu____8680)
                     -> flatten1 e1
                 | uu____8721 ->
                     let uu____8722 =
                       let uu____8727 =
                         let uu____8728 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____8728
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____8727)  in
                     FStar_Errors.raise_err uu____8722
                  in
               let uu____8743 = flatten1 t_head  in
               (match uu____8743 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____8817 =
                          let uu____8822 =
                            let uu____8823 = FStar_Util.string_of_int n1  in
                            let uu____8830 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____8841 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____8823 uu____8830 uu____8841
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____8822)
                           in
                        FStar_Errors.raise_err uu____8817)
                     else ();
                     (let uu____8849 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____8849 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____8902 args1 =
                            match uu____8902 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____9002 =
                                       let uu____9003 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____9003.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____9002
                                 | (binders3,[]) ->
                                     let uu____9041 =
                                       let uu____9042 =
                                         let uu____9045 =
                                           let uu____9046 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____9046
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____9045
                                          in
                                       uu____9042.FStar_Syntax_Syntax.n  in
                                     (match uu____9041 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____9079 =
                                            let uu____9080 =
                                              let uu____9081 =
                                                let uu____9096 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____9096)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____9081
                                               in
                                            mk1 uu____9080  in
                                          N uu____9079
                                      | uu____9109 -> failwith "wat?")
                                 | ([],uu____9110::uu____9111) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____9163)::binders3,(arg,uu____9166)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____9253 = FStar_List.splitAt n' binders1  in
                          (match uu____9253 with
                           | (binders2,uu____9291) ->
                               let uu____9324 =
                                 let uu____9347 =
                                   FStar_List.map2
                                     (fun uu____9409  ->
                                        fun uu____9410  ->
                                          match (uu____9409, uu____9410) with
                                          | ((bv,uu____9458),(arg,q)) ->
                                              let uu____9487 =
                                                let uu____9488 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____9488.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____9487 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9509 ->
                                                   let uu____9510 =
                                                     let uu____9517 =
                                                       star_type' env arg  in
                                                     (uu____9517, q)  in
                                                   (uu____9510, [(arg, q)])
                                               | uu____9554 ->
                                                   let uu____9555 =
                                                     check_n env arg  in
                                                   (match uu____9555 with
                                                    | (uu____9580,s_arg,u_arg)
                                                        ->
                                                        let uu____9583 =
                                                          let uu____9592 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____9592
                                                          then
                                                            let uu____9601 =
                                                              let uu____9608
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____9608, q)
                                                               in
                                                            [uu____9601;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____9583))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____9347  in
                               (match uu____9324 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____9735 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____9748 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____9735, uu____9748)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____9814) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____9820) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____9826,uu____9827) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____9869 = let uu____9870 = env.tc_const c  in N uu____9870
             in
          (uu____9869, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____9877 ->
          let uu____9890 =
            let uu____9891 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____9891  in
          failwith uu____9890
      | FStar_Syntax_Syntax.Tm_type uu____9898 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____9905 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____9926 ->
          let uu____9933 =
            let uu____9934 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____9934  in
          failwith uu____9933
      | FStar_Syntax_Syntax.Tm_uvar uu____9941 ->
          let uu____9954 =
            let uu____9955 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____9955  in
          failwith uu____9954
      | FStar_Syntax_Syntax.Tm_delayed uu____9962 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____9991 =
            let uu____9992 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____9992  in
          failwith uu____9991

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
          let uu____10039 = check_n env e0  in
          match uu____10039 with
          | (uu____10052,s_e0,u_e0) ->
              let uu____10055 =
                let uu____10084 =
                  FStar_List.map
                    (fun b  ->
                       let uu____10145 = FStar_Syntax_Subst.open_branch b  in
                       match uu____10145 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___369_10187 = env  in
                             let uu____10188 =
                               let uu____10189 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____10189
                                in
                             {
                               env = uu____10188;
                               subst = (uu___369_10187.subst);
                               tc_const = (uu___369_10187.tc_const)
                             }  in
                           let uu____10192 = f env1 body  in
                           (match uu____10192 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____10264 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____10084  in
              (match uu____10055 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____10368 = FStar_List.hd nms  in
                     match uu____10368 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___352_10376  ->
                          match uu___352_10376 with
                          | M uu____10377 -> true
                          | uu____10378 -> false) nms
                      in
                   let uu____10379 =
                     let uu____10416 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____10506  ->
                              match uu____10506 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____10683 =
                                         check env original_body (M t2)  in
                                       (match uu____10683 with
                                        | (uu____10720,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____10759,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____10416  in
                   (match uu____10379 with
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
                              (fun uu____10943  ->
                                 match uu____10943 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____10994 =
                                         let uu____10995 =
                                           let uu____11012 =
                                             let uu____11023 =
                                               let uu____11032 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____11035 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____11032, uu____11035)  in
                                             [uu____11023]  in
                                           (s_body, uu____11012)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____10995
                                          in
                                       mk1 uu____10994  in
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
                            let uu____11169 =
                              let uu____11170 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11170]  in
                            let uu____11189 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____11169 uu____11189
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____11213 =
                              let uu____11222 =
                                let uu____11229 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____11229
                                 in
                              [uu____11222]  in
                            let uu____11248 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____11213 uu____11248
                             in
                          let uu____11251 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____11290 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____11251, uu____11290)
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
                           let uu____11399 =
                             let uu____11400 =
                               let uu____11401 =
                                 let uu____11428 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____11428,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11401
                                in
                             mk1 uu____11400  in
                           let uu____11487 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____11399, uu____11487))))

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
              let uu____11552 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____11552]  in
            let uu____11571 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____11571 with
            | (x_binders1,e21) ->
                let uu____11584 = infer env e1  in
                (match uu____11584 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____11601 = is_C t1  in
                       if uu____11601
                       then
                         let uu___370_11602 = binding  in
                         let uu____11603 =
                           let uu____11606 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____11606  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___370_11602.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___370_11602.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11603;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___370_11602.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___370_11602.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___370_11602.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___370_11602.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___371_11609 = env  in
                       let uu____11610 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___372_11612 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___372_11612.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___372_11612.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____11610;
                         subst = (uu___371_11609.subst);
                         tc_const = (uu___371_11609.tc_const)
                       }  in
                     let uu____11613 = proceed env1 e21  in
                     (match uu____11613 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___373_11630 = binding  in
                            let uu____11631 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___373_11630.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___373_11630.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11631;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___373_11630.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___373_11630.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___373_11630.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___373_11630.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____11634 =
                            let uu____11635 =
                              let uu____11636 =
                                let uu____11649 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___374_11663 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___374_11663.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___374_11663.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___374_11663.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___374_11663.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___374_11663.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___374_11663.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11649)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11636  in
                            mk1 uu____11635  in
                          let uu____11664 =
                            let uu____11665 =
                              let uu____11666 =
                                let uu____11679 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___375_11693 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___375_11693.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___375_11693.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___375_11693.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___375_11693.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___375_11693.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___375_11693.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11679)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11666  in
                            mk1 uu____11665  in
                          (nm_rec, uu____11634, uu____11664))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___376_11698 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___376_11698.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___376_11698.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___376_11698.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___376_11698.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___376_11698.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___377_11700 = env  in
                       let uu____11701 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___378_11703 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___378_11703.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___378_11703.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____11701;
                         subst = (uu___377_11700.subst);
                         tc_const = (uu___377_11700.tc_const)
                       }  in
                     let uu____11704 = ensure_m env1 e21  in
                     (match uu____11704 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____11727 =
                              let uu____11728 =
                                let uu____11745 =
                                  let uu____11756 =
                                    let uu____11765 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____11768 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____11765, uu____11768)  in
                                  [uu____11756]  in
                                (s_e2, uu____11745)  in
                              FStar_Syntax_Syntax.Tm_app uu____11728  in
                            mk1 uu____11727  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____11809 =
                              let uu____11810 =
                                let uu____11827 =
                                  let uu____11838 =
                                    let uu____11847 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____11847)  in
                                  [uu____11838]  in
                                (s_e1, uu____11827)  in
                              FStar_Syntax_Syntax.Tm_app uu____11810  in
                            mk1 uu____11809  in
                          let uu____11882 =
                            let uu____11883 =
                              let uu____11884 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____11884]  in
                            FStar_Syntax_Util.abs uu____11883 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____11903 =
                            let uu____11904 =
                              let uu____11905 =
                                let uu____11918 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___379_11932 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___379_11932.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___379_11932.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___379_11932.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___379_11932.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___379_11932.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___379_11932.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11918)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____11905  in
                            mk1 uu____11904  in
                          ((M t2), uu____11882, uu____11903)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____11942 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____11942  in
      let uu____11943 = check env e mn  in
      match uu____11943 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____11959 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____11981 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____11981  in
      let uu____11982 = check env e mn  in
      match uu____11982 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____11998 -> failwith "[check_m]: impossible"

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
        (let uu____12030 =
           let uu____12031 = is_C c  in Prims.op_Negation uu____12031  in
         if uu____12030 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____12041 =
           let uu____12042 = FStar_Syntax_Subst.compress c  in
           uu____12042.FStar_Syntax_Syntax.n  in
         match uu____12041 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____12071 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____12071 with
              | (wp_head,wp_args) ->
                  ((let uu____12115 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____12133 =
                           let uu____12134 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____12134
                            in
                         Prims.op_Negation uu____12133)
                       in
                    if uu____12115 then failwith "mismatch" else ());
                   (let uu____12144 =
                      let uu____12145 =
                        let uu____12162 =
                          FStar_List.map2
                            (fun uu____12200  ->
                               fun uu____12201  ->
                                 match (uu____12200, uu____12201) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____12262 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____12262
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____12265 =
                                         let uu____12266 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____12266 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____12265
                                       then
                                         let uu____12267 =
                                           let uu____12272 =
                                             let uu____12273 =
                                               print_implicit q  in
                                             let uu____12274 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____12273 uu____12274
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____12272)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____12267
                                       else ());
                                      (let uu____12276 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____12276, q)))) args wp_args
                           in
                        (head1, uu____12162)  in
                      FStar_Syntax_Syntax.Tm_app uu____12145  in
                    mk1 uu____12144)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____12322 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____12322 with
              | (binders_orig,comp1) ->
                  let uu____12329 =
                    let uu____12346 =
                      FStar_List.map
                        (fun uu____12386  ->
                           match uu____12386 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____12414 = is_C h  in
                               if uu____12414
                               then
                                 let w' =
                                   let uu____12428 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____12428
                                    in
                                 let uu____12429 =
                                   let uu____12438 =
                                     let uu____12447 =
                                       let uu____12454 =
                                         let uu____12455 =
                                           let uu____12456 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____12456  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12455
                                          in
                                       (uu____12454, q)  in
                                     [uu____12447]  in
                                   (w', q) :: uu____12438  in
                                 (w', uu____12429)
                               else
                                 (let x =
                                    let uu____12489 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____12489
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____12346  in
                  (match uu____12329 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____12562 =
                           let uu____12565 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12565
                            in
                         FStar_Syntax_Subst.subst_comp uu____12562 comp1  in
                       let app =
                         let uu____12569 =
                           let uu____12570 =
                             let uu____12587 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____12606 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____12607 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____12606, uu____12607)) bvs
                                in
                             (wp, uu____12587)  in
                           FStar_Syntax_Syntax.Tm_app uu____12570  in
                         mk1 uu____12569  in
                       let comp3 =
                         let uu____12621 = type_of_comp comp2  in
                         let uu____12622 = is_monadic_comp comp2  in
                         trans_G env uu____12621 uu____12622 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____12624,uu____12625) ->
             trans_F_ env e wp
         | uu____12666 -> failwith "impossible trans_F_")

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
            let uu____12671 =
              let uu____12672 = star_type' env h  in
              let uu____12675 =
                let uu____12686 =
                  let uu____12695 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____12695)  in
                [uu____12686]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____12672;
                FStar_Syntax_Syntax.effect_args = uu____12675;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____12671
          else
            (let uu____12719 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____12719)

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
    fun t  -> let uu____12738 = n env.env t  in star_type' env uu____12738
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____12757 = n env.env t  in check_n env uu____12757
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____12773 = n env.env c  in
        let uu____12774 = n env.env wp  in
        trans_F_ env uu____12773 uu____12774
  