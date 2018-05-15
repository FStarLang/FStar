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
              let uu___101_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___101_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___101_123.FStar_Syntax_Syntax.index);
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
               let uu____150 =
                 let uu____151 =
                   let uu____154 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____154
                    in
                 uu____151.FStar_Syntax_Syntax.n  in
               match uu____150 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____183) -> t1
                     | uu____192 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____193 = collect_binders rest  in
                   FStar_List.append bs uu____193
               | FStar_Syntax_Syntax.Tm_type uu____204 -> []
               | uu____209 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____229 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____229 FStar_Syntax_Util.name_binders
                in
             (let uu____249 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____249
              then
                let uu____250 =
                  let uu____251 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____251  in
                d uu____250
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____285 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____285 with
                | (sigelt,fv) ->
                    ((let uu____293 =
                        let uu____296 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____296
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____293);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____426  ->
                     match uu____426 with
                     | (t,b) ->
                         let uu____437 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____437))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____470 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____470))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____495 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____495)
                 in
              let uu____496 =
                let uu____513 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____537 =
                        let uu____540 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____540  in
                      FStar_Syntax_Util.arrow gamma uu____537  in
                    let uu____541 =
                      let uu____542 =
                        let uu____549 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____554 =
                          let uu____561 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____561]  in
                        uu____549 :: uu____554  in
                      FStar_List.append binders uu____542  in
                    FStar_Syntax_Util.abs uu____541 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____582 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____583 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____582, uu____583)  in
                match uu____513 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____623 =
                        let uu____624 =
                          let uu____639 =
                            let uu____648 =
                              FStar_List.map
                                (fun uu____668  ->
                                   match uu____668 with
                                   | (bv,uu____678) ->
                                       let uu____679 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____680 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____679, uu____680)) binders
                               in
                            let uu____681 =
                              let uu____688 =
                                let uu____693 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____694 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____693, uu____694)  in
                              let uu____695 =
                                let uu____702 =
                                  let uu____707 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____707)  in
                                [uu____702]  in
                              uu____688 :: uu____695  in
                            FStar_List.append uu____648 uu____681  in
                          (fv, uu____639)  in
                        FStar_Syntax_Syntax.Tm_app uu____624  in
                      mk1 uu____623  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____496 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____776 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____776
                       in
                    let ret1 =
                      let uu____780 =
                        let uu____781 =
                          let uu____784 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____784  in
                        FStar_Syntax_Util.residual_tot uu____781  in
                      FStar_Pervasives_Native.Some uu____780  in
                    let body =
                      let uu____788 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____788 ret1  in
                    let uu____791 =
                      let uu____792 = mk_all_implicit binders  in
                      let uu____799 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____792 uu____799  in
                    FStar_Syntax_Util.abs uu____791 body ret1  in
                  let c_pure1 =
                    let uu____827 = mk_lid "pure"  in
                    register env1 uu____827 c_pure  in
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
                      let uu____834 =
                        let uu____835 =
                          let uu____836 =
                            let uu____843 =
                              let uu____848 =
                                let uu____849 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____849
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____848  in
                            [uu____843]  in
                          let uu____858 =
                            let uu____861 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____861  in
                          FStar_Syntax_Util.arrow uu____836 uu____858  in
                        mk_gctx uu____835  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____834
                       in
                    let r =
                      let uu____863 =
                        let uu____864 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____864  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____863
                       in
                    let ret1 =
                      let uu____868 =
                        let uu____869 =
                          let uu____872 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____872  in
                        FStar_Syntax_Util.residual_tot uu____869  in
                      FStar_Pervasives_Native.Some uu____868  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____882 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____885 =
                          let uu____894 =
                            let uu____897 =
                              let uu____898 =
                                let uu____899 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____899
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____898  in
                            [uu____897]  in
                          FStar_List.append gamma_as_args uu____894  in
                        FStar_Syntax_Util.mk_app uu____882 uu____885  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____902 =
                      let uu____903 = mk_all_implicit binders  in
                      let uu____910 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____903 uu____910  in
                    FStar_Syntax_Util.abs uu____902 outer_body ret1  in
                  let c_app1 =
                    let uu____946 = mk_lid "app"  in
                    register env1 uu____946 c_app  in
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
                      let uu____955 =
                        let uu____962 =
                          let uu____967 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____967  in
                        [uu____962]  in
                      let uu____976 =
                        let uu____979 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____979  in
                      FStar_Syntax_Util.arrow uu____955 uu____976  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____982 =
                        let uu____983 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____983  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____982
                       in
                    let ret1 =
                      let uu____987 =
                        let uu____988 =
                          let uu____991 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____991  in
                        FStar_Syntax_Util.residual_tot uu____988  in
                      FStar_Pervasives_Native.Some uu____987  in
                    let uu____992 =
                      let uu____993 = mk_all_implicit binders  in
                      let uu____1000 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____993 uu____1000  in
                    let uu____1035 =
                      let uu____1038 =
                        let uu____1047 =
                          let uu____1050 =
                            let uu____1051 =
                              let uu____1060 =
                                let uu____1063 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1063]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1060
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1051  in
                          let uu____1070 =
                            let uu____1073 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1073]  in
                          uu____1050 :: uu____1070  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1047
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1038  in
                    FStar_Syntax_Util.abs uu____992 uu____1035 ret1  in
                  let c_lift11 =
                    let uu____1081 = mk_lid "lift1"  in
                    register env1 uu____1081 c_lift1  in
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
                      let uu____1091 =
                        let uu____1098 =
                          let uu____1103 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1103  in
                        let uu____1104 =
                          let uu____1111 =
                            let uu____1116 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1116  in
                          [uu____1111]  in
                        uu____1098 :: uu____1104  in
                      let uu____1129 =
                        let uu____1132 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1132  in
                      FStar_Syntax_Util.arrow uu____1091 uu____1129  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1135 =
                        let uu____1136 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1136  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1135
                       in
                    let a2 =
                      let uu____1138 =
                        let uu____1139 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1139  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1138
                       in
                    let ret1 =
                      let uu____1143 =
                        let uu____1144 =
                          let uu____1147 = FStar_Syntax_Syntax.bv_to_name t3
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
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1149 uu____1156  in
                    let uu____1199 =
                      let uu____1202 =
                        let uu____1211 =
                          let uu____1214 =
                            let uu____1215 =
                              let uu____1224 =
                                let uu____1227 =
                                  let uu____1228 =
                                    let uu____1237 =
                                      let uu____1240 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1240]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1237
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1228
                                   in
                                let uu____1247 =
                                  let uu____1250 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1250]  in
                                uu____1227 :: uu____1247  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1224
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1215  in
                          let uu____1257 =
                            let uu____1260 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1260]  in
                          uu____1214 :: uu____1257  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1211
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1202  in
                    FStar_Syntax_Util.abs uu____1148 uu____1199 ret1  in
                  let c_lift21 =
                    let uu____1268 = mk_lid "lift2"  in
                    register env1 uu____1268 c_lift2  in
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
                      let uu____1277 =
                        let uu____1284 =
                          let uu____1289 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1289  in
                        [uu____1284]  in
                      let uu____1298 =
                        let uu____1301 =
                          let uu____1302 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1302  in
                        FStar_Syntax_Syntax.mk_Total uu____1301  in
                      FStar_Syntax_Util.arrow uu____1277 uu____1298  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1307 =
                        let uu____1308 =
                          let uu____1311 =
                            let uu____1312 =
                              let uu____1319 =
                                let uu____1324 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1324
                                 in
                              [uu____1319]  in
                            let uu____1333 =
                              let uu____1336 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1336  in
                            FStar_Syntax_Util.arrow uu____1312 uu____1333  in
                          mk_ctx uu____1311  in
                        FStar_Syntax_Util.residual_tot uu____1308  in
                      FStar_Pervasives_Native.Some uu____1307  in
                    let e1 =
                      let uu____1338 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1338
                       in
                    let body =
                      let uu____1342 =
                        let uu____1343 =
                          let uu____1350 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1350]  in
                        FStar_List.append gamma uu____1343  in
                      let uu____1367 =
                        let uu____1370 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1373 =
                          let uu____1382 =
                            let uu____1383 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1383  in
                          let uu____1384 = args_of_binders1 gamma  in
                          uu____1382 :: uu____1384  in
                        FStar_Syntax_Util.mk_app uu____1370 uu____1373  in
                      FStar_Syntax_Util.abs uu____1342 uu____1367 ret1  in
                    let uu____1387 =
                      let uu____1388 = mk_all_implicit binders  in
                      let uu____1395 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1388 uu____1395  in
                    FStar_Syntax_Util.abs uu____1387 body ret1  in
                  let c_push1 =
                    let uu____1427 = mk_lid "push"  in
                    register env1 uu____1427 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1449 =
                        let uu____1450 =
                          let uu____1465 = args_of_binders1 binders  in
                          (c, uu____1465)  in
                        FStar_Syntax_Syntax.Tm_app uu____1450  in
                      mk1 uu____1449
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1489 =
                        let uu____1490 =
                          let uu____1497 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1502 =
                            let uu____1509 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1509]  in
                          uu____1497 :: uu____1502  in
                        let uu____1526 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1490 uu____1526  in
                      FStar_Syntax_Syntax.mk_Total uu____1489  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1530 =
                      let uu____1531 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1531  in
                    let uu____1542 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1546 =
                        let uu____1549 =
                          let uu____1558 =
                            let uu____1561 =
                              let uu____1562 =
                                let uu____1571 =
                                  let uu____1578 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1578  in
                                [uu____1571]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1562  in
                            [uu____1561]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1558
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1549  in
                      FStar_Syntax_Util.ascribe uu____1546
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1530 uu____1542
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1616 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1616 wp_if_then_else  in
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
                      let uu____1629 =
                        let uu____1638 =
                          let uu____1641 =
                            let uu____1642 =
                              let uu____1651 =
                                let uu____1654 =
                                  let uu____1655 =
                                    let uu____1664 =
                                      let uu____1671 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1671
                                       in
                                    [uu____1664]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1655
                                   in
                                [uu____1654]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1651
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1642  in
                          let uu____1690 =
                            let uu____1693 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1693]  in
                          uu____1641 :: uu____1690  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1638
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1629  in
                    let uu____1700 =
                      let uu____1701 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1701  in
                    FStar_Syntax_Util.abs uu____1700 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1713 = mk_lid "wp_assert"  in
                    register env1 uu____1713 wp_assert  in
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
                      let uu____1726 =
                        let uu____1735 =
                          let uu____1738 =
                            let uu____1739 =
                              let uu____1748 =
                                let uu____1751 =
                                  let uu____1752 =
                                    let uu____1761 =
                                      let uu____1768 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1768
                                       in
                                    [uu____1761]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1752
                                   in
                                [uu____1751]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1748
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1739  in
                          let uu____1787 =
                            let uu____1790 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1790]  in
                          uu____1738 :: uu____1787  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1735
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1726  in
                    let uu____1797 =
                      let uu____1798 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1798  in
                    FStar_Syntax_Util.abs uu____1797 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1810 = mk_lid "wp_assume"  in
                    register env1 uu____1810 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1821 =
                        let uu____1828 =
                          let uu____1833 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1833  in
                        [uu____1828]  in
                      let uu____1842 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1821 uu____1842  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1849 =
                        let uu____1858 =
                          let uu____1861 =
                            let uu____1862 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1862  in
                          let uu____1877 =
                            let uu____1880 =
                              let uu____1881 =
                                let uu____1890 =
                                  let uu____1893 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1893]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1890
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1881  in
                            [uu____1880]  in
                          uu____1861 :: uu____1877  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1858
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1849  in
                    let uu____1906 =
                      let uu____1907 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1907  in
                    FStar_Syntax_Util.abs uu____1906 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1919 = mk_lid "wp_close"  in
                    register env1 uu____1919 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1929 =
                      let uu____1930 =
                        let uu____1931 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1931
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1930  in
                    FStar_Pervasives_Native.Some uu____1929  in
                  let mk_forall1 x body =
                    let uu____1943 =
                      let uu____1950 =
                        let uu____1951 =
                          let uu____1966 =
                            let uu____1975 =
                              let uu____1982 =
                                let uu____1983 =
                                  let uu____1984 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1984]  in
                                FStar_Syntax_Util.abs uu____1983 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1982  in
                            [uu____1975]  in
                          (FStar_Syntax_Util.tforall, uu____1966)  in
                        FStar_Syntax_Syntax.Tm_app uu____1951  in
                      FStar_Syntax_Syntax.mk uu____1950  in
                    uu____1943 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2032 =
                      let uu____2033 = FStar_Syntax_Subst.compress t  in
                      uu____2033.FStar_Syntax_Syntax.n  in
                    match uu____2032 with
                    | FStar_Syntax_Syntax.Tm_type uu____2036 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2062  ->
                              match uu____2062 with
                              | (b,uu____2068) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2069 -> true  in
                  let rec is_monotonic t =
                    let uu____2080 =
                      let uu____2081 = FStar_Syntax_Subst.compress t  in
                      uu____2081.FStar_Syntax_Syntax.n  in
                    match uu____2080 with
                    | FStar_Syntax_Syntax.Tm_type uu____2084 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2110  ->
                              match uu____2110 with
                              | (b,uu____2116) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2117 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2191 =
                      let uu____2192 = FStar_Syntax_Subst.compress t1  in
                      uu____2192.FStar_Syntax_Syntax.n  in
                    match uu____2191 with
                    | FStar_Syntax_Syntax.Tm_type uu____2197 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2200);
                                      FStar_Syntax_Syntax.pos = uu____2201;
                                      FStar_Syntax_Syntax.vars = uu____2202;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2236 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2236
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2243 =
                              let uu____2246 =
                                let uu____2255 =
                                  let uu____2262 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2262  in
                                [uu____2255]  in
                              FStar_Syntax_Util.mk_app x uu____2246  in
                            let uu____2275 =
                              let uu____2278 =
                                let uu____2287 =
                                  let uu____2294 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2294  in
                                [uu____2287]  in
                              FStar_Syntax_Util.mk_app y uu____2278  in
                            mk_rel1 b uu____2243 uu____2275  in
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
                             let uu____2311 =
                               let uu____2314 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2317 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2314 uu____2317  in
                             let uu____2320 =
                               let uu____2323 =
                                 let uu____2326 =
                                   let uu____2335 =
                                     let uu____2342 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2342
                                      in
                                   [uu____2335]  in
                                 FStar_Syntax_Util.mk_app x uu____2326  in
                               let uu____2355 =
                                 let uu____2358 =
                                   let uu____2367 =
                                     let uu____2374 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2374
                                      in
                                   [uu____2367]  in
                                 FStar_Syntax_Util.mk_app y uu____2358  in
                               mk_rel1 b uu____2323 uu____2355  in
                             FStar_Syntax_Util.mk_imp uu____2311 uu____2320
                              in
                           let uu____2387 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2387)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2390);
                                      FStar_Syntax_Syntax.pos = uu____2391;
                                      FStar_Syntax_Syntax.vars = uu____2392;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2426 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2426
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2433 =
                              let uu____2436 =
                                let uu____2445 =
                                  let uu____2452 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2452  in
                                [uu____2445]  in
                              FStar_Syntax_Util.mk_app x uu____2436  in
                            let uu____2465 =
                              let uu____2468 =
                                let uu____2477 =
                                  let uu____2484 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2484  in
                                [uu____2477]  in
                              FStar_Syntax_Util.mk_app y uu____2468  in
                            mk_rel1 b uu____2433 uu____2465  in
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
                             let uu____2501 =
                               let uu____2504 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2507 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2504 uu____2507  in
                             let uu____2510 =
                               let uu____2513 =
                                 let uu____2516 =
                                   let uu____2525 =
                                     let uu____2532 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2532
                                      in
                                   [uu____2525]  in
                                 FStar_Syntax_Util.mk_app x uu____2516  in
                               let uu____2545 =
                                 let uu____2548 =
                                   let uu____2557 =
                                     let uu____2564 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2564
                                      in
                                   [uu____2557]  in
                                 FStar_Syntax_Util.mk_app y uu____2548  in
                               mk_rel1 b uu____2513 uu____2545  in
                             FStar_Syntax_Util.mk_imp uu____2501 uu____2510
                              in
                           let uu____2577 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2577)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___102_2608 = t1  in
                          let uu____2609 =
                            let uu____2610 =
                              let uu____2623 =
                                let uu____2626 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2626  in
                              ([binder], uu____2623)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2610  in
                          {
                            FStar_Syntax_Syntax.n = uu____2609;
                            FStar_Syntax_Syntax.pos =
                              (uu___102_2608.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___102_2608.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2643 ->
                        failwith "unhandled arrow"
                    | uu____2658 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____2693 =
                        let uu____2694 = FStar_Syntax_Subst.compress t1  in
                        uu____2694.FStar_Syntax_Syntax.n  in
                      match uu____2693 with
                      | FStar_Syntax_Syntax.Tm_type uu____2697 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2720 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2720
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2739 =
                                let uu____2740 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2740 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2739
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2761 =
                            let uu____2772 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2788  ->
                                     match uu____2788 with
                                     | (t2,q) ->
                                         let uu____2801 = project i x  in
                                         let uu____2804 = project i y  in
                                         mk_stronger t2 uu____2801 uu____2804)
                                args
                               in
                            match uu____2772 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2761 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2857);
                                      FStar_Syntax_Syntax.pos = uu____2858;
                                      FStar_Syntax_Syntax.vars = uu____2859;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2897  ->
                                   match uu____2897 with
                                   | (bv,q) ->
                                       let uu____2904 =
                                         let uu____2905 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2905  in
                                       FStar_Syntax_Syntax.gen_bv uu____2904
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2912 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2912) bvs
                             in
                          let body =
                            let uu____2914 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2917 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2914 uu____2917  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2926);
                                      FStar_Syntax_Syntax.pos = uu____2927;
                                      FStar_Syntax_Syntax.vars = uu____2928;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2966  ->
                                   match uu____2966 with
                                   | (bv,q) ->
                                       let uu____2973 =
                                         let uu____2974 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2974  in
                                       FStar_Syntax_Syntax.gen_bv uu____2973
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2981 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2981) bvs
                             in
                          let body =
                            let uu____2983 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2986 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2983 uu____2986  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2993 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2995 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2998 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3001 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2995 uu____2998 uu____3001  in
                    let uu____3004 =
                      let uu____3005 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3005  in
                    FStar_Syntax_Util.abs uu____3004 body ret_tot_type  in
                  let stronger1 =
                    let uu____3033 = mk_lid "stronger"  in
                    register env1 uu____3033 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3039 = FStar_Util.prefix gamma  in
                    match uu____3039 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3088 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3088
                             in
                          let uu____3091 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3091 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3101 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3101  in
                              let guard_free1 =
                                let uu____3111 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3111  in
                              let pat =
                                let uu____3115 =
                                  let uu____3124 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3124]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3115
                                 in
                              let pattern_guarded_body =
                                let uu____3146 =
                                  let uu____3147 =
                                    let uu____3154 =
                                      let uu____3155 =
                                        let uu____3166 =
                                          let uu____3175 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3175]  in
                                        [uu____3166]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3155
                                       in
                                    (body, uu____3154)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3147  in
                                mk1 uu____3146  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3212 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3220 =
                            let uu____3223 =
                              let uu____3224 =
                                let uu____3227 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3230 =
                                  let uu____3239 = args_of_binders1 wp_args
                                     in
                                  let uu____3242 =
                                    let uu____3245 =
                                      let uu____3246 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3246
                                       in
                                    [uu____3245]  in
                                  FStar_List.append uu____3239 uu____3242  in
                                FStar_Syntax_Util.mk_app uu____3227
                                  uu____3230
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3224  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3223
                             in
                          FStar_Syntax_Util.abs gamma uu____3220
                            ret_gtot_type
                           in
                        let uu____3247 =
                          let uu____3248 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3248  in
                        FStar_Syntax_Util.abs uu____3247 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3260 = mk_lid "wp_ite"  in
                    register env1 uu____3260 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3266 = FStar_Util.prefix gamma  in
                    match uu____3266 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3309 =
                            let uu____3310 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3315 =
                              let uu____3324 =
                                let uu____3331 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3331  in
                              [uu____3324]  in
                            FStar_Syntax_Util.mk_app uu____3310 uu____3315
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3309
                           in
                        let uu____3344 =
                          let uu____3345 =
                            let uu____3352 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3352 gamma  in
                          FStar_List.append binders uu____3345  in
                        FStar_Syntax_Util.abs uu____3344 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3368 = mk_lid "null_wp"  in
                    register env1 uu____3368 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3379 =
                        let uu____3388 =
                          let uu____3391 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3392 =
                            let uu____3395 =
                              let uu____3396 =
                                let uu____3405 =
                                  let uu____3412 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3412  in
                                [uu____3405]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3396
                               in
                            let uu____3425 =
                              let uu____3428 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3428]  in
                            uu____3395 :: uu____3425  in
                          uu____3391 :: uu____3392  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3388
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3379  in
                    let uu____3435 =
                      let uu____3436 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3436  in
                    FStar_Syntax_Util.abs uu____3435 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3448 = mk_lid "wp_trivial"  in
                    register env1 uu____3448 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3453 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3453
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____3460 =
                      let uu____3461 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____3461  in
                    let uu____3513 =
                      let uu___103_3514 = ed  in
                      let uu____3515 =
                        let uu____3516 = c wp_if_then_else2  in
                        ([], uu____3516)  in
                      let uu____3523 =
                        let uu____3524 = c wp_ite2  in ([], uu____3524)  in
                      let uu____3531 =
                        let uu____3532 = c stronger2  in ([], uu____3532)  in
                      let uu____3539 =
                        let uu____3540 = c wp_close2  in ([], uu____3540)  in
                      let uu____3547 =
                        let uu____3548 = c wp_assert2  in ([], uu____3548)
                         in
                      let uu____3555 =
                        let uu____3556 = c wp_assume2  in ([], uu____3556)
                         in
                      let uu____3563 =
                        let uu____3564 = c null_wp2  in ([], uu____3564)  in
                      let uu____3571 =
                        let uu____3572 = c wp_trivial2  in ([], uu____3572)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_3514.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_3514.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_3514.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_3514.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_3514.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_3514.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_3514.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3515;
                        FStar_Syntax_Syntax.ite_wp = uu____3523;
                        FStar_Syntax_Syntax.stronger = uu____3531;
                        FStar_Syntax_Syntax.close_wp = uu____3539;
                        FStar_Syntax_Syntax.assert_p = uu____3547;
                        FStar_Syntax_Syntax.assume_p = uu____3555;
                        FStar_Syntax_Syntax.null_wp = uu____3563;
                        FStar_Syntax_Syntax.trivial = uu____3571;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_3514.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_3514.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_3514.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_3514.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___103_3514.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____3460, uu____3513)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_3594 = dmff_env  in
      {
        env = env';
        subst = (uu___104_3594.subst);
        tc_const = (uu___104_3594.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____3611 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____3625 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___90_3637  ->
    match uu___90_3637 with
    | FStar_Syntax_Syntax.Total (t,uu____3639) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___89_3652  ->
                match uu___89_3652 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3653 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____3655 =
          let uu____3656 =
            let uu____3657 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3657
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3656  in
        failwith uu____3655
    | FStar_Syntax_Syntax.GTotal uu____3658 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___91_3671  ->
    match uu___91_3671 with
    | N t ->
        let uu____3673 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____3673
    | M t ->
        let uu____3675 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____3675
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3681,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____3683;
                      FStar_Syntax_Syntax.vars = uu____3684;_})
        -> nm_of_comp n2
    | uu____3701 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____3711 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3711 with | M uu____3712 -> true | N uu____3713 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3719 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3733 =
        let uu____3740 =
          let uu____3745 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3745  in
        [uu____3740]  in
      let uu____3758 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3733 uu____3758  in
    let uu____3761 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3761
  
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
        let uu____3802 =
          let uu____3803 =
            let uu____3816 =
              let uu____3823 =
                let uu____3828 =
                  let uu____3829 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____3829  in
                let uu____3830 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____3828, uu____3830)  in
              [uu____3823]  in
            let uu____3839 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____3816, uu____3839)  in
          FStar_Syntax_Syntax.Tm_arrow uu____3803  in
        mk1 uu____3802

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3877) ->
          let binders1 =
            FStar_List.map
              (fun uu____3913  ->
                 match uu____3913 with
                 | (bv,aqual) ->
                     let uu____3924 =
                       let uu___105_3925 = bv  in
                       let uu____3926 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_3925.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_3925.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3926
                       }  in
                     (uu____3924, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3929,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3931);
                             FStar_Syntax_Syntax.pos = uu____3932;
                             FStar_Syntax_Syntax.vars = uu____3933;_})
               ->
               let uu____3958 =
                 let uu____3959 =
                   let uu____3972 =
                     let uu____3975 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3975  in
                   (binders1, uu____3972)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3959  in
               mk1 uu____3958
           | uu____3984 ->
               let uu____3985 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3985 with
                | N hn ->
                    let uu____3987 =
                      let uu____3988 =
                        let uu____4001 =
                          let uu____4004 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4004  in
                        (binders1, uu____4001)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3988  in
                    mk1 uu____3987
                | M a ->
                    let uu____4014 =
                      let uu____4015 =
                        let uu____4028 =
                          let uu____4035 =
                            let uu____4042 =
                              let uu____4047 =
                                let uu____4048 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4048  in
                              let uu____4049 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4047, uu____4049)  in
                            [uu____4042]  in
                          FStar_List.append binders1 uu____4035  in
                        let uu____4062 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4028, uu____4062)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4015  in
                    mk1 uu____4014))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4144 = f x  in
                    FStar_Util.string_builder_append strb uu____4144);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4151 = f x1  in
                         FStar_Util.string_builder_append strb uu____4151))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4153 =
              let uu____4158 =
                let uu____4159 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4160 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4159 uu____4160
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4158)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4153  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4176 =
              let uu____4177 = FStar_Syntax_Subst.compress ty  in
              uu____4177.FStar_Syntax_Syntax.n  in
            match uu____4176 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4198 =
                  let uu____4199 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4199  in
                if uu____4198
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____4233 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____4233 s  in
                       let uu____4236 =
                         let uu____4237 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____4237  in
                       if uu____4236
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____4240 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____4240 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____4262  ->
                                  match uu____4262 with
                                  | (bv,uu____4272) ->
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
            | uu____4286 ->
                ((let uu____4288 =
                    let uu____4293 =
                      let uu____4294 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4294
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4293)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4288);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4305 =
              let uu____4306 = FStar_Syntax_Subst.compress head2  in
              uu____4306.FStar_Syntax_Syntax.n  in
            match uu____4305 with
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
                  (let uu____4311 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4311)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4313 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4313 with
                 | ((uu____4322,ty),uu____4324) ->
                     let uu____4329 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4329
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.env t1
                          in
                       let uu____4337 =
                         let uu____4338 = FStar_Syntax_Subst.compress res  in
                         uu____4338.FStar_Syntax_Syntax.n  in
                       (match uu____4337 with
                        | FStar_Syntax_Syntax.Tm_app uu____4341 -> true
                        | uu____4356 ->
                            ((let uu____4358 =
                                let uu____4363 =
                                  let uu____4364 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____4364
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____4363)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____4358);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____4366 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4367 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4369) ->
                is_valid_application t2
            | uu____4374 -> false  in
          let uu____4375 = is_valid_application head1  in
          if uu____4375
          then
            let uu____4376 =
              let uu____4377 =
                let uu____4392 =
                  FStar_List.map
                    (fun uu____4415  ->
                       match uu____4415 with
                       | (t2,qual) ->
                           let uu____4432 = star_type' env t2  in
                           (uu____4432, qual)) args
                   in
                (head1, uu____4392)  in
              FStar_Syntax_Syntax.Tm_app uu____4377  in
            mk1 uu____4376
          else
            (let uu____4444 =
               let uu____4449 =
                 let uu____4450 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____4450
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____4449)  in
             FStar_Errors.raise_err uu____4444)
      | FStar_Syntax_Syntax.Tm_bvar uu____4451 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____4452 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____4453 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____4454 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____4478 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____4478 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___108_4486 = env  in
                 let uu____4487 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____4487;
                   subst = (uu___108_4486.subst);
                   tc_const = (uu___108_4486.tc_const)
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
               ((let uu___109_4509 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_4509.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_4509.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____4516 =
            let uu____4517 =
              let uu____4524 = star_type' env t2  in (uu____4524, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____4517  in
          mk1 uu____4516
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____4576 =
            let uu____4577 =
              let uu____4604 = star_type' env e  in
              let uu____4607 =
                let uu____4624 =
                  let uu____4633 = star_type' env t2  in
                  FStar_Util.Inl uu____4633  in
                (uu____4624, FStar_Pervasives_Native.None)  in
              (uu____4604, uu____4607, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4577  in
          mk1 uu____4576
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____4721 =
            let uu____4722 =
              let uu____4749 = star_type' env e  in
              let uu____4752 =
                let uu____4769 =
                  let uu____4778 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4778  in
                (uu____4769, FStar_Pervasives_Native.None)  in
              (uu____4749, uu____4752, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4722  in
          mk1 uu____4721
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4819,(uu____4820,FStar_Pervasives_Native.Some uu____4821),uu____4822)
          ->
          let uu____4871 =
            let uu____4876 =
              let uu____4877 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4877
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4876)  in
          FStar_Errors.raise_err uu____4871
      | FStar_Syntax_Syntax.Tm_refine uu____4878 ->
          let uu____4885 =
            let uu____4890 =
              let uu____4891 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4891
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4890)  in
          FStar_Errors.raise_err uu____4885
      | FStar_Syntax_Syntax.Tm_uinst uu____4892 ->
          let uu____4899 =
            let uu____4904 =
              let uu____4905 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4905
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4904)  in
          FStar_Errors.raise_err uu____4899
      | FStar_Syntax_Syntax.Tm_quoted uu____4906 ->
          let uu____4913 =
            let uu____4918 =
              let uu____4919 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4919
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4918)  in
          FStar_Errors.raise_err uu____4913
      | FStar_Syntax_Syntax.Tm_constant uu____4920 ->
          let uu____4921 =
            let uu____4926 =
              let uu____4927 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4927
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4926)  in
          FStar_Errors.raise_err uu____4921
      | FStar_Syntax_Syntax.Tm_match uu____4928 ->
          let uu____4951 =
            let uu____4956 =
              let uu____4957 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4957
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4956)  in
          FStar_Errors.raise_err uu____4951
      | FStar_Syntax_Syntax.Tm_let uu____4958 ->
          let uu____4971 =
            let uu____4976 =
              let uu____4977 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4977
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4976)  in
          FStar_Errors.raise_err uu____4971
      | FStar_Syntax_Syntax.Tm_uvar uu____4978 ->
          let uu____4993 =
            let uu____4998 =
              let uu____4999 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4999
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4998)  in
          FStar_Errors.raise_err uu____4993
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5000 =
            let uu____5005 =
              let uu____5006 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5006
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5005)  in
          FStar_Errors.raise_err uu____5000
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5008 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5008
      | FStar_Syntax_Syntax.Tm_delayed uu____5011 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___93_5042  ->
    match uu___93_5042 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___92_5049  ->
                match uu___92_5049 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5050 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5056 =
      let uu____5057 = FStar_Syntax_Subst.compress t  in
      uu____5057.FStar_Syntax_Syntax.n  in
    match uu____5056 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5083 =
            let uu____5084 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5084  in
          is_C uu____5083  in
        if r
        then
          ((let uu____5100 =
              let uu____5101 =
                FStar_List.for_all
                  (fun uu____5109  ->
                     match uu____5109 with | (h,uu____5115) -> is_C h) args
                 in
              Prims.op_Negation uu____5101  in
            if uu____5100 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5119 =
              let uu____5120 =
                FStar_List.for_all
                  (fun uu____5129  ->
                     match uu____5129 with
                     | (h,uu____5135) ->
                         let uu____5136 = is_C h  in
                         Prims.op_Negation uu____5136) args
                 in
              Prims.op_Negation uu____5120  in
            if uu____5119 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5156 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5156 with
         | M t1 ->
             ((let uu____5159 = is_C t1  in
               if uu____5159 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5163) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5169) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5175,uu____5176) -> is_C t1
    | uu____5217 -> false
  
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
          let uu____5250 =
            let uu____5251 =
              let uu____5266 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____5269 =
                let uu____5278 =
                  let uu____5285 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____5285)  in
                [uu____5278]  in
              (uu____5266, uu____5269)  in
            FStar_Syntax_Syntax.Tm_app uu____5251  in
          mk1 uu____5250  in
        let uu____5310 =
          let uu____5311 = FStar_Syntax_Syntax.mk_binder p  in [uu____5311]
           in
        FStar_Syntax_Util.abs uu____5310 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___94_5328  ->
    match uu___94_5328 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5329 -> false
  
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
        let return_if uu____5564 =
          match uu____5564 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____5601 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____5603 =
                       let uu____5604 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____5604  in
                     Prims.op_Negation uu____5603)
                   in
                if uu____5601
                then
                  let uu____5605 =
                    let uu____5610 =
                      let uu____5611 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____5612 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____5613 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____5611 uu____5612 uu____5613
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____5610)  in
                  FStar_Errors.raise_err uu____5605
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____5634 = mk_return env t1 s_e  in
                     ((M t1), uu____5634, u_e)))
               | (M t1,N t2) ->
                   let uu____5641 =
                     let uu____5646 =
                       let uu____5647 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____5648 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____5649 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____5647 uu____5648 uu____5649
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____5646)
                      in
                   FStar_Errors.raise_err uu____5641)
           in
        let ensure_m env1 e2 =
          let strip_m uu___95_5698 =
            match uu___95_5698 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____5714 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____5734 =
                let uu____5739 =
                  let uu____5740 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____5740
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____5739)  in
              FStar_Errors.raise_error uu____5734 e2.FStar_Syntax_Syntax.pos
          | M uu____5747 ->
              let uu____5748 = check env1 e2 context_nm  in
              strip_m uu____5748
           in
        let uu____5755 =
          let uu____5756 = FStar_Syntax_Subst.compress e  in
          uu____5756.FStar_Syntax_Syntax.n  in
        match uu____5755 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5765 ->
            let uu____5766 = infer env e  in return_if uu____5766
        | FStar_Syntax_Syntax.Tm_name uu____5773 ->
            let uu____5774 = infer env e  in return_if uu____5774
        | FStar_Syntax_Syntax.Tm_fvar uu____5781 ->
            let uu____5782 = infer env e  in return_if uu____5782
        | FStar_Syntax_Syntax.Tm_abs uu____5789 ->
            let uu____5806 = infer env e  in return_if uu____5806
        | FStar_Syntax_Syntax.Tm_constant uu____5813 ->
            let uu____5814 = infer env e  in return_if uu____5814
        | FStar_Syntax_Syntax.Tm_quoted uu____5821 ->
            let uu____5828 = infer env e  in return_if uu____5828
        | FStar_Syntax_Syntax.Tm_app uu____5835 ->
            let uu____5850 = infer env e  in return_if uu____5850
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5858 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5858 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5920) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5926) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5932,uu____5933) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5974 ->
            let uu____5987 =
              let uu____5988 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5988  in
            failwith uu____5987
        | FStar_Syntax_Syntax.Tm_type uu____5995 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6002 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6021 ->
            let uu____6028 =
              let uu____6029 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6029  in
            failwith uu____6028
        | FStar_Syntax_Syntax.Tm_uvar uu____6036 ->
            let uu____6051 =
              let uu____6052 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6052  in
            failwith uu____6051
        | FStar_Syntax_Syntax.Tm_delayed uu____6059 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6090 =
              let uu____6091 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6091  in
            failwith uu____6090

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
      let uu____6119 =
        let uu____6120 = FStar_Syntax_Subst.compress e  in
        uu____6120.FStar_Syntax_Syntax.n  in
      match uu____6119 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6138 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6138
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6185;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____6186;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6192 =
                  let uu___110_6193 = rc  in
                  let uu____6194 =
                    let uu____6199 =
                      let uu____6202 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____6202  in
                    FStar_Pervasives_Native.Some uu____6199  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___110_6193.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6194;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___110_6193.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____6192
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___111_6214 = env  in
            let uu____6215 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____6215;
              subst = (uu___111_6214.subst);
              tc_const = (uu___111_6214.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____6235  ->
                 match uu____6235 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___112_6248 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___112_6248.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___112_6248.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____6249 =
            FStar_List.fold_left
              (fun uu____6278  ->
                 fun uu____6279  ->
                   match (uu____6278, uu____6279) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____6327 = is_C c  in
                       if uu____6327
                       then
                         let xw =
                           let uu____6335 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____6335
                            in
                         let x =
                           let uu___113_6337 = bv  in
                           let uu____6338 =
                             let uu____6341 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____6341  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___113_6337.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___113_6337.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____6338
                           }  in
                         let env3 =
                           let uu___114_6343 = env2  in
                           let uu____6344 =
                             let uu____6347 =
                               let uu____6348 =
                                 let uu____6355 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____6355)  in
                               FStar_Syntax_Syntax.NT uu____6348  in
                             uu____6347 :: (env2.subst)  in
                           {
                             env = (uu___114_6343.env);
                             subst = uu____6344;
                             tc_const = (uu___114_6343.tc_const)
                           }  in
                         let uu____6360 =
                           let uu____6363 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____6364 =
                             let uu____6367 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____6367 :: acc  in
                           uu____6363 :: uu____6364  in
                         (env3, uu____6360)
                       else
                         (let x =
                            let uu___115_6372 = bv  in
                            let uu____6373 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___115_6372.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___115_6372.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____6373
                            }  in
                          let uu____6376 =
                            let uu____6379 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____6379 :: acc  in
                          (env2, uu____6376))) (env1, []) binders1
             in
          (match uu____6249 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____6399 =
                 let check_what =
                   let uu____6425 = is_monadic rc_opt1  in
                   if uu____6425 then check_m else check_n  in
                 let uu____6439 = check_what env2 body1  in
                 match uu____6439 with
                 | (t,s_body,u_body) ->
                     let uu____6459 =
                       let uu____6462 =
                         let uu____6463 = is_monadic rc_opt1  in
                         if uu____6463 then M t else N t  in
                       comp_of_nm uu____6462  in
                     (uu____6459, s_body, u_body)
                  in
               (match uu____6399 with
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
                                 let uu____6500 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___96_6504  ->
                                           match uu___96_6504 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____6505 -> false))
                                    in
                                 if uu____6500
                                 then
                                   let uu____6506 =
                                     FStar_List.filter
                                       (fun uu___97_6510  ->
                                          match uu___97_6510 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____6511 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____6506
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____6520 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___98_6524  ->
                                         match uu___98_6524 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____6525 -> false))
                                  in
                               if uu____6520
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___99_6532  ->
                                        match uu___99_6532 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____6533 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____6534 =
                                   let uu____6535 =
                                     let uu____6540 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____6540
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____6535 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____6534
                               else
                                 (let uu____6546 =
                                    let uu___116_6547 = rc  in
                                    let uu____6548 =
                                      let uu____6553 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____6553
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___116_6547.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____6548;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___116_6547.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____6546))
                       in
                    let uu____6558 =
                      let comp1 =
                        let uu____6566 = is_monadic rc_opt1  in
                        let uu____6567 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____6566 uu____6567
                         in
                      let uu____6568 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____6568,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____6558 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____6606 =
                             let uu____6607 =
                               let uu____6624 =
                                 let uu____6627 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____6627 s_rc_opt  in
                               (s_binders1, s_body1, uu____6624)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6607  in
                           mk1 uu____6606  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____6645 =
                             let uu____6646 =
                               let uu____6663 =
                                 let uu____6666 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____6666 u_rc_opt  in
                               (u_binders2, u_body2, uu____6663)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6646  in
                           mk1 uu____6645  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____6680;_};
            FStar_Syntax_Syntax.fv_delta = uu____6681;
            FStar_Syntax_Syntax.fv_qual = uu____6682;_}
          ->
          let uu____6685 =
            let uu____6690 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6690  in
          (match uu____6685 with
           | (uu____6721,t) ->
               let uu____6723 =
                 let uu____6724 = normalize1 t  in N uu____6724  in
               (uu____6723, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6725;
             FStar_Syntax_Syntax.vars = uu____6726;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6789 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6789 with
           | (unary_op,uu____6811) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6870;
             FStar_Syntax_Syntax.vars = uu____6871;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6947 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6947 with
           | (unary_op,uu____6969) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7034;
             FStar_Syntax_Syntax.vars = uu____7035;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____7065 = infer env a  in
          (match uu____7065 with
           | (t,s,u) ->
               let uu____7081 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7081 with
                | (head1,uu____7103) ->
                    let uu____7124 =
                      let uu____7125 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____7125  in
                    let uu____7126 =
                      let uu____7127 =
                        let uu____7128 =
                          let uu____7143 =
                            let uu____7152 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7152]  in
                          (head1, uu____7143)  in
                        FStar_Syntax_Syntax.Tm_app uu____7128  in
                      mk1 uu____7127  in
                    let uu____7181 =
                      let uu____7182 =
                        let uu____7183 =
                          let uu____7198 =
                            let uu____7207 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7207]  in
                          (head1, uu____7198)  in
                        FStar_Syntax_Syntax.Tm_app uu____7183  in
                      mk1 uu____7182  in
                    (uu____7124, uu____7126, uu____7181)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7236;
             FStar_Syntax_Syntax.vars = uu____7237;_},(a1,uu____7239)::a2::[])
          ->
          let uu____7281 = infer env a1  in
          (match uu____7281 with
           | (t,s,u) ->
               let uu____7297 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7297 with
                | (head1,uu____7319) ->
                    let uu____7340 =
                      let uu____7341 =
                        let uu____7342 =
                          let uu____7357 =
                            let uu____7366 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7366; a2]  in
                          (head1, uu____7357)  in
                        FStar_Syntax_Syntax.Tm_app uu____7342  in
                      mk1 uu____7341  in
                    let uu____7401 =
                      let uu____7402 =
                        let uu____7403 =
                          let uu____7418 =
                            let uu____7427 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7427; a2]  in
                          (head1, uu____7418)  in
                        FStar_Syntax_Syntax.Tm_app uu____7403  in
                      mk1 uu____7402  in
                    (t, uu____7340, uu____7401)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7462;
             FStar_Syntax_Syntax.vars = uu____7463;_},uu____7464)
          ->
          let uu____7485 =
            let uu____7490 =
              let uu____7491 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7491
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7490)  in
          FStar_Errors.raise_error uu____7485 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7498;
             FStar_Syntax_Syntax.vars = uu____7499;_},uu____7500)
          ->
          let uu____7521 =
            let uu____7526 =
              let uu____7527 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7527
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7526)  in
          FStar_Errors.raise_error uu____7521 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____7556 = check_n env head1  in
          (match uu____7556 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____7578 =
                   let uu____7579 = FStar_Syntax_Subst.compress t  in
                   uu____7579.FStar_Syntax_Syntax.n  in
                 match uu____7578 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____7582 -> true
                 | uu____7595 -> false  in
               let rec flatten1 t =
                 let uu____7614 =
                   let uu____7615 = FStar_Syntax_Subst.compress t  in
                   uu____7615.FStar_Syntax_Syntax.n  in
                 match uu____7614 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____7632);
                                FStar_Syntax_Syntax.pos = uu____7633;
                                FStar_Syntax_Syntax.vars = uu____7634;_})
                     when is_arrow t1 ->
                     let uu____7659 = flatten1 t1  in
                     (match uu____7659 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7741,uu____7742)
                     -> flatten1 e1
                 | uu____7783 ->
                     let uu____7784 =
                       let uu____7789 =
                         let uu____7790 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____7790
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____7789)  in
                     FStar_Errors.raise_err uu____7784
                  in
               let uu____7803 = flatten1 t_head  in
               (match uu____7803 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____7863 =
                          let uu____7868 =
                            let uu____7869 = FStar_Util.string_of_int n1  in
                            let uu____7876 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____7887 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____7869 uu____7876 uu____7887
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____7868)
                           in
                        FStar_Errors.raise_err uu____7863)
                     else ();
                     (let uu____7895 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____7895 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____7944 args1 =
                            match uu____7944 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____8024 =
                                       let uu____8025 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____8025.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____8024
                                 | (binders3,[]) ->
                                     let uu____8055 =
                                       let uu____8056 =
                                         let uu____8059 =
                                           let uu____8060 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____8060
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____8059
                                          in
                                       uu____8056.FStar_Syntax_Syntax.n  in
                                     (match uu____8055 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____8087 =
                                            let uu____8088 =
                                              let uu____8089 =
                                                let uu____8102 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____8102)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____8089
                                               in
                                            mk1 uu____8088  in
                                          N uu____8087
                                      | uu____8113 -> failwith "wat?")
                                 | ([],uu____8114::uu____8115) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____8155)::binders3,(arg,uu____8158)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____8221 = FStar_List.splitAt n' binders1  in
                          (match uu____8221 with
                           | (binders2,uu____8253) ->
                               let uu____8278 =
                                 let uu____8297 =
                                   FStar_List.map2
                                     (fun uu____8347  ->
                                        fun uu____8348  ->
                                          match (uu____8347, uu____8348) with
                                          | ((bv,uu____8384),(arg,q)) ->
                                              let uu____8401 =
                                                let uu____8402 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____8402.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____8401 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____8419 ->
                                                   let uu____8420 =
                                                     let uu____8425 =
                                                       star_type' env arg  in
                                                     (uu____8425, q)  in
                                                   (uu____8420, [(arg, q)])
                                               | uu____8450 ->
                                                   let uu____8451 =
                                                     check_n env arg  in
                                                   (match uu____8451 with
                                                    | (uu____8472,s_arg,u_arg)
                                                        ->
                                                        let uu____8475 =
                                                          let uu____8482 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____8482
                                                          then
                                                            let uu____8489 =
                                                              let uu____8494
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____8494, q)
                                                               in
                                                            [uu____8489;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____8475))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____8297  in
                               (match uu____8278 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____8583 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____8594 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____8583, uu____8594)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____8658) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____8664) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8670,uu____8671) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____8713 = let uu____8714 = env.tc_const c  in N uu____8714
             in
          (uu____8713, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____8721 ->
          let uu____8734 =
            let uu____8735 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____8735  in
          failwith uu____8734
      | FStar_Syntax_Syntax.Tm_type uu____8742 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____8749 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____8768 ->
          let uu____8775 =
            let uu____8776 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____8776  in
          failwith uu____8775
      | FStar_Syntax_Syntax.Tm_uvar uu____8783 ->
          let uu____8798 =
            let uu____8799 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____8799  in
          failwith uu____8798
      | FStar_Syntax_Syntax.Tm_delayed uu____8806 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____8837 =
            let uu____8838 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8838  in
          failwith uu____8837

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
          let uu____8885 = check_n env e0  in
          match uu____8885 with
          | (uu____8898,s_e0,u_e0) ->
              let uu____8901 =
                let uu____8930 =
                  FStar_List.map
                    (fun b  ->
                       let uu____8991 = FStar_Syntax_Subst.open_branch b  in
                       match uu____8991 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___117_9033 = env  in
                             let uu____9034 =
                               let uu____9035 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____9035
                                in
                             {
                               env = uu____9034;
                               subst = (uu___117_9033.subst);
                               tc_const = (uu___117_9033.tc_const)
                             }  in
                           let uu____9038 = f env1 body  in
                           (match uu____9038 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____9110 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____8930  in
              (match uu____8901 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____9214 = FStar_List.hd nms  in
                     match uu____9214 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_9222  ->
                          match uu___100_9222 with
                          | M uu____9223 -> true
                          | uu____9224 -> false) nms
                      in
                   let uu____9225 =
                     let uu____9262 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____9352  ->
                              match uu____9352 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____9529 =
                                         check env original_body (M t2)  in
                                       (match uu____9529 with
                                        | (uu____9566,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____9605,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____9262  in
                   (match uu____9225 with
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
                              (fun uu____9789  ->
                                 match uu____9789 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____9840 =
                                         let uu____9841 =
                                           let uu____9856 =
                                             let uu____9865 =
                                               let uu____9872 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____9875 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____9872, uu____9875)  in
                                             [uu____9865]  in
                                           (s_body, uu____9856)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____9841
                                          in
                                       mk1 uu____9840  in
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
                            let uu____9999 =
                              let uu____10000 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10000]  in
                            let uu____10013 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____9999 uu____10013
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____10037 =
                              let uu____10044 =
                                let uu____10049 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____10049
                                 in
                              [uu____10044]  in
                            let uu____10062 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____10037 uu____10062
                             in
                          let uu____10065 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____10104 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____10065, uu____10104)
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
                           let uu____10213 =
                             let uu____10214 =
                               let uu____10215 =
                                 let uu____10242 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____10242,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10215
                                in
                             mk1 uu____10214  in
                           let uu____10301 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____10213, uu____10301))))

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
              let uu____10364 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10364]  in
            let uu____10377 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____10377 with
            | (x_binders1,e21) ->
                let uu____10390 = infer env e1  in
                (match uu____10390 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____10407 = is_C t1  in
                       if uu____10407
                       then
                         let uu___118_10408 = binding  in
                         let uu____10409 =
                           let uu____10412 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____10412  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___118_10408.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___118_10408.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____10409;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___118_10408.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___118_10408.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___118_10408.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___118_10408.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___119_10415 = env  in
                       let uu____10416 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___120_10418 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___120_10418.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___120_10418.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10416;
                         subst = (uu___119_10415.subst);
                         tc_const = (uu___119_10415.tc_const)
                       }  in
                     let uu____10419 = proceed env1 e21  in
                     (match uu____10419 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___121_10436 = binding  in
                            let uu____10437 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___121_10436.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___121_10436.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____10437;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___121_10436.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___121_10436.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___121_10436.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___121_10436.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____10440 =
                            let uu____10441 =
                              let uu____10442 =
                                let uu____10455 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___122_10469 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_10469.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_10469.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_10469.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_10469.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___122_10469.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___122_10469.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10455)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10442  in
                            mk1 uu____10441  in
                          let uu____10470 =
                            let uu____10471 =
                              let uu____10472 =
                                let uu____10485 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___123_10499 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_10499.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_10499.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_10499.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_10499.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___123_10499.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___123_10499.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10485)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10472  in
                            mk1 uu____10471  in
                          (nm_rec, uu____10440, uu____10470))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___124_10504 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___124_10504.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___124_10504.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___124_10504.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___124_10504.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___124_10504.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___125_10506 = env  in
                       let uu____10507 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___126_10509 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_10509.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_10509.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10507;
                         subst = (uu___125_10506.subst);
                         tc_const = (uu___125_10506.tc_const)
                       }  in
                     let uu____10510 = ensure_m env1 e21  in
                     (match uu____10510 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____10533 =
                              let uu____10534 =
                                let uu____10549 =
                                  let uu____10558 =
                                    let uu____10565 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____10568 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____10565, uu____10568)  in
                                  [uu____10558]  in
                                (s_e2, uu____10549)  in
                              FStar_Syntax_Syntax.Tm_app uu____10534  in
                            mk1 uu____10533  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____10599 =
                              let uu____10600 =
                                let uu____10615 =
                                  let uu____10624 =
                                    let uu____10631 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____10631)  in
                                  [uu____10624]  in
                                (s_e1, uu____10615)  in
                              FStar_Syntax_Syntax.Tm_app uu____10600  in
                            mk1 uu____10599  in
                          let uu____10656 =
                            let uu____10657 =
                              let uu____10658 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10658]  in
                            FStar_Syntax_Util.abs uu____10657 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____10671 =
                            let uu____10672 =
                              let uu____10673 =
                                let uu____10686 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___127_10700 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___127_10700.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___127_10700.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___127_10700.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___127_10700.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___127_10700.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___127_10700.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10686)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10673  in
                            mk1 uu____10672  in
                          ((M t2), uu____10656, uu____10671)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10710 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____10710  in
      let uu____10711 = check env e mn  in
      match uu____10711 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10727 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10749 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____10749  in
      let uu____10750 = check env e mn  in
      match uu____10750 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10766 -> failwith "[check_m]: impossible"

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
        (let uu____10796 =
           let uu____10797 = is_C c  in Prims.op_Negation uu____10797  in
         if uu____10796 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____10807 =
           let uu____10808 = FStar_Syntax_Subst.compress c  in
           uu____10808.FStar_Syntax_Syntax.n  in
         match uu____10807 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____10833 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____10833 with
              | (wp_head,wp_args) ->
                  ((let uu____10871 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____10885 =
                           let uu____10886 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____10886
                            in
                         Prims.op_Negation uu____10885)
                       in
                    if uu____10871 then failwith "mismatch" else ());
                   (let uu____10894 =
                      let uu____10895 =
                        let uu____10910 =
                          FStar_List.map2
                            (fun uu____10940  ->
                               fun uu____10941  ->
                                 match (uu____10940, uu____10941) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____10980 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____10980
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____10983 =
                                           let uu____10988 =
                                             let uu____10989 =
                                               print_implicit q  in
                                             let uu____10990 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____10989 uu____10990
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____10988)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____10983)
                                      else ();
                                      (let uu____10992 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____10992, q)))) args wp_args
                           in
                        (head1, uu____10910)  in
                      FStar_Syntax_Syntax.Tm_app uu____10895  in
                    mk1 uu____10894)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____11028 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____11028 with
              | (binders_orig,comp1) ->
                  let uu____11035 =
                    let uu____11050 =
                      FStar_List.map
                        (fun uu____11084  ->
                           match uu____11084 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____11104 = is_C h  in
                               if uu____11104
                               then
                                 let w' =
                                   let uu____11116 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____11116
                                    in
                                 let uu____11117 =
                                   let uu____11124 =
                                     let uu____11131 =
                                       let uu____11136 =
                                         let uu____11137 =
                                           let uu____11138 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____11138  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____11137
                                          in
                                       (uu____11136, q)  in
                                     [uu____11131]  in
                                   (w', q) :: uu____11124  in
                                 (w', uu____11117)
                               else
                                 (let x =
                                    let uu____11159 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____11159
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____11050  in
                  (match uu____11035 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____11214 =
                           let uu____11217 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____11217
                            in
                         FStar_Syntax_Subst.subst_comp uu____11214 comp1  in
                       let app =
                         let uu____11221 =
                           let uu____11222 =
                             let uu____11237 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____11254 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____11255 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____11254, uu____11255)) bvs
                                in
                             (wp, uu____11237)  in
                           FStar_Syntax_Syntax.Tm_app uu____11222  in
                         mk1 uu____11221  in
                       let comp3 =
                         let uu____11267 = type_of_comp comp2  in
                         let uu____11268 = is_monadic_comp comp2  in
                         trans_G env uu____11267 uu____11268 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____11270,uu____11271) ->
             trans_F_ env e wp
         | uu____11312 -> failwith "impossible trans_F_")

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
            let uu____11317 =
              let uu____11318 = star_type' env h  in
              let uu____11321 =
                let uu____11330 =
                  let uu____11337 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____11337)  in
                [uu____11330]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____11318;
                FStar_Syntax_Syntax.effect_args = uu____11321;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____11317
          else
            (let uu____11353 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____11353)

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
    fun t  -> let uu____11372 = n env.env t  in star_type' env uu____11372
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____11391 = n env.env t  in check_n env uu____11391
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____11407 = n env.env c  in
        let uu____11408 = n env.env wp  in
        trans_F_ env uu____11407 uu____11408
  