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
              let uu___344_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___344_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___344_123.FStar_Syntax_Syntax.index);
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
                          let uu___345_2608 = t1  in
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
                              (uu___345_2608.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___345_2608.FStar_Syntax_Syntax.vars)
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
                    match FStar_Util.prefix gamma with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3073 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3073
                             in
                          let uu____3076 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3076 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3086 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3086  in
                              let guard_free1 =
                                let uu____3096 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3096  in
                              let pat =
                                let uu____3100 =
                                  let uu____3109 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3109]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3100
                                 in
                              let pattern_guarded_body =
                                let uu____3131 =
                                  let uu____3132 =
                                    let uu____3139 =
                                      let uu____3140 =
                                        let uu____3151 =
                                          let uu____3160 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3160]  in
                                        [uu____3151]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3140
                                       in
                                    (body, uu____3139)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3132  in
                                mk1 uu____3131  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3197 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3205 =
                            let uu____3208 =
                              let uu____3209 =
                                let uu____3212 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3215 =
                                  let uu____3224 = args_of_binders1 wp_args
                                     in
                                  let uu____3227 =
                                    let uu____3230 =
                                      let uu____3231 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3231
                                       in
                                    [uu____3230]  in
                                  FStar_List.append uu____3224 uu____3227  in
                                FStar_Syntax_Util.mk_app uu____3212
                                  uu____3215
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3209  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3208
                             in
                          FStar_Syntax_Util.abs gamma uu____3205
                            ret_gtot_type
                           in
                        let uu____3232 =
                          let uu____3233 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3233  in
                        FStar_Syntax_Util.abs uu____3232 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3245 = mk_lid "wp_ite"  in
                    register env1 uu____3245 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    match FStar_Util.prefix gamma with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3279 =
                            let uu____3280 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3285 =
                              let uu____3294 =
                                let uu____3301 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3301  in
                              [uu____3294]  in
                            FStar_Syntax_Util.mk_app uu____3280 uu____3285
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3279
                           in
                        let uu____3314 =
                          let uu____3315 =
                            let uu____3322 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3322 gamma  in
                          FStar_List.append binders uu____3315  in
                        FStar_Syntax_Util.abs uu____3314 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3338 = mk_lid "null_wp"  in
                    register env1 uu____3338 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3349 =
                        let uu____3358 =
                          let uu____3361 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3362 =
                            let uu____3365 =
                              let uu____3366 =
                                let uu____3375 =
                                  let uu____3382 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3382  in
                                [uu____3375]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3366
                               in
                            let uu____3395 =
                              let uu____3398 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3398]  in
                            uu____3365 :: uu____3395  in
                          uu____3361 :: uu____3362  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3358
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3349  in
                    let uu____3405 =
                      let uu____3406 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3406  in
                    FStar_Syntax_Util.abs uu____3405 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3418 = mk_lid "wp_trivial"  in
                    register env1 uu____3418 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3423 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3423
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____3430 =
                      let uu____3431 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____3431  in
                    let uu____3483 =
                      let uu___346_3484 = ed  in
                      let uu____3485 =
                        let uu____3486 = c wp_if_then_else2  in
                        ([], uu____3486)  in
                      let uu____3493 =
                        let uu____3494 = c wp_ite2  in ([], uu____3494)  in
                      let uu____3501 =
                        let uu____3502 = c stronger2  in ([], uu____3502)  in
                      let uu____3509 =
                        let uu____3510 = c wp_close2  in ([], uu____3510)  in
                      let uu____3517 =
                        let uu____3518 = c wp_assert2  in ([], uu____3518)
                         in
                      let uu____3525 =
                        let uu____3526 = c wp_assume2  in ([], uu____3526)
                         in
                      let uu____3533 =
                        let uu____3534 = c null_wp2  in ([], uu____3534)  in
                      let uu____3541 =
                        let uu____3542 = c wp_trivial2  in ([], uu____3542)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___346_3484.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___346_3484.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___346_3484.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___346_3484.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___346_3484.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___346_3484.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___346_3484.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3485;
                        FStar_Syntax_Syntax.ite_wp = uu____3493;
                        FStar_Syntax_Syntax.stronger = uu____3501;
                        FStar_Syntax_Syntax.close_wp = uu____3509;
                        FStar_Syntax_Syntax.assert_p = uu____3517;
                        FStar_Syntax_Syntax.assume_p = uu____3525;
                        FStar_Syntax_Syntax.null_wp = uu____3533;
                        FStar_Syntax_Syntax.trivial = uu____3541;
                        FStar_Syntax_Syntax.repr =
                          (uu___346_3484.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___346_3484.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___346_3484.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___346_3484.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___346_3484.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____3430, uu____3483)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___347_3564 = dmff_env  in
      {
        env = env';
        subst = (uu___347_3564.subst);
        tc_const = (uu___347_3564.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____3581 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____3595 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___333_3607  ->
    match uu___333_3607 with
    | FStar_Syntax_Syntax.Total (t,uu____3609) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___332_3622  ->
                match uu___332_3622 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3623 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____3625 =
          let uu____3626 =
            let uu____3627 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3627
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3626  in
        failwith uu____3625
    | FStar_Syntax_Syntax.GTotal uu____3628 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___334_3641  ->
    match uu___334_3641 with
    | N t ->
        let uu____3643 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____3643
    | M t ->
        let uu____3645 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____3645
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3651,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____3653;
                      FStar_Syntax_Syntax.vars = uu____3654;_})
        -> nm_of_comp n2
    | uu____3671 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____3681 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3681 with | M uu____3682 -> true | N uu____3683 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3689 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3703 =
        let uu____3710 =
          let uu____3715 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3715  in
        [uu____3710]  in
      let uu____3728 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3703 uu____3728  in
    let uu____3731 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3731
  
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
        let uu____3772 =
          let uu____3773 =
            let uu____3786 =
              let uu____3793 =
                let uu____3798 =
                  let uu____3799 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____3799  in
                let uu____3800 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____3798, uu____3800)  in
              [uu____3793]  in
            let uu____3809 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____3786, uu____3809)  in
          FStar_Syntax_Syntax.Tm_arrow uu____3773  in
        mk1 uu____3772

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
      let raise_err1 msg =
        FStar_Errors.raise_error msg t1.FStar_Syntax_Syntax.pos  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3861) ->
          let binders1 =
            FStar_List.map
              (fun uu____3897  ->
                 match uu____3897 with
                 | (bv,aqual) ->
                     let uu____3908 =
                       let uu___348_3909 = bv  in
                       let uu____3910 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___348_3909.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___348_3909.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3910
                       }  in
                     (uu____3908, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3913,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3915);
                             FStar_Syntax_Syntax.pos = uu____3916;
                             FStar_Syntax_Syntax.vars = uu____3917;_})
               ->
               let uu____3942 =
                 let uu____3943 =
                   let uu____3956 =
                     let uu____3959 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3959  in
                   (binders1, uu____3956)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3943  in
               mk1 uu____3942
           | uu____3968 ->
               let uu____3969 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3969 with
                | N hn ->
                    let uu____3971 =
                      let uu____3972 =
                        let uu____3985 =
                          let uu____3988 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3988  in
                        (binders1, uu____3985)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3972  in
                    mk1 uu____3971
                | M a ->
                    let uu____3998 =
                      let uu____3999 =
                        let uu____4012 =
                          let uu____4019 =
                            let uu____4026 =
                              let uu____4031 =
                                let uu____4032 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4032  in
                              let uu____4033 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4031, uu____4033)  in
                            [uu____4026]  in
                          FStar_List.append binders1 uu____4019  in
                        let uu____4046 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4012, uu____4046)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3999  in
                    mk1 uu____3998))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4128 = f x  in
                    FStar_Util.string_builder_append strb uu____4128);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4135 = f x1  in
                         FStar_Util.string_builder_append strb uu____4135))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4137 =
              let uu____4142 =
                let uu____4143 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4144 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4143 uu____4144
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4142)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4137  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4160 =
              let uu____4161 = FStar_Syntax_Subst.compress ty  in
              uu____4161.FStar_Syntax_Syntax.n  in
            match uu____4160 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4182 =
                  let uu____4183 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4183  in
                if uu____4182
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____4217 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____4217 s  in
                       let uu____4220 =
                         let uu____4221 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____4221  in
                       if uu____4220
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____4224 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____4224 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____4246  ->
                                  match uu____4246 with
                                  | (bv,uu____4256) ->
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
            | uu____4270 ->
                ((let uu____4272 =
                    let uu____4277 =
                      let uu____4278 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4278
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4277)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4272);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4289 =
              let uu____4290 = FStar_Syntax_Subst.compress head2  in
              uu____4290.FStar_Syntax_Syntax.n  in
            match uu____4289 with
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
                  (let uu____4295 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4295)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4297 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4297 with
                 | ((uu____4306,ty),uu____4308) ->
                     let uu____4313 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4313
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.env t1
                          in
                       let uu____4321 =
                         let uu____4322 = FStar_Syntax_Subst.compress res  in
                         uu____4322.FStar_Syntax_Syntax.n  in
                       (match uu____4321 with
                        | FStar_Syntax_Syntax.Tm_app uu____4325 -> true
                        | uu____4340 ->
                            ((let uu____4342 =
                                let uu____4347 =
                                  let uu____4348 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____4348
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____4347)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____4342);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____4350 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4351 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4353) ->
                is_valid_application t2
            | uu____4358 -> false  in
          let uu____4359 = is_valid_application head1  in
          if uu____4359
          then
            let uu____4360 =
              let uu____4361 =
                let uu____4376 =
                  FStar_List.map
                    (fun uu____4399  ->
                       match uu____4399 with
                       | (t2,qual) ->
                           let uu____4416 = star_type' env t2  in
                           (uu____4416, qual)) args
                   in
                (head1, uu____4376)  in
              FStar_Syntax_Syntax.Tm_app uu____4361  in
            mk1 uu____4360
          else
            (let uu____4428 =
               let uu____4433 =
                 let uu____4434 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____4434
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____4433)  in
             raise_err1 uu____4428)
      | FStar_Syntax_Syntax.Tm_bvar uu____4435 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____4436 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____4437 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____4438 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____4462 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____4462 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___351_4470 = env  in
                 let uu____4471 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____4471;
                   subst = (uu___351_4470.subst);
                   tc_const = (uu___351_4470.tc_const)
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
               ((let uu___352_4493 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___352_4493.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___352_4493.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____4500 =
            let uu____4501 =
              let uu____4508 = star_type' env t2  in (uu____4508, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____4501  in
          mk1 uu____4500
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____4560 =
            let uu____4561 =
              let uu____4588 = star_type' env e  in
              let uu____4591 =
                let uu____4608 =
                  let uu____4617 = star_type' env t2  in
                  FStar_Util.Inl uu____4617  in
                (uu____4608, FStar_Pervasives_Native.None)  in
              (uu____4588, uu____4591, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4561  in
          mk1 uu____4560
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____4705 =
            let uu____4706 =
              let uu____4733 = star_type' env e  in
              let uu____4736 =
                let uu____4753 =
                  let uu____4762 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4762  in
                (uu____4753, FStar_Pervasives_Native.None)  in
              (uu____4733, uu____4736, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4706  in
          mk1 uu____4705
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4803,(uu____4804,FStar_Pervasives_Native.Some uu____4805),uu____4806)
          ->
          let uu____4855 =
            let uu____4860 =
              let uu____4861 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4861
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4860)  in
          raise_err1 uu____4855
      | FStar_Syntax_Syntax.Tm_refine uu____4862 ->
          let uu____4869 =
            let uu____4874 =
              let uu____4875 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4875
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4874)  in
          raise_err1 uu____4869
      | FStar_Syntax_Syntax.Tm_uinst uu____4876 ->
          let uu____4883 =
            let uu____4888 =
              let uu____4889 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4889
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4888)  in
          raise_err1 uu____4883
      | FStar_Syntax_Syntax.Tm_quoted uu____4890 ->
          let uu____4897 =
            let uu____4902 =
              let uu____4903 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4903
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4902)  in
          raise_err1 uu____4897
      | FStar_Syntax_Syntax.Tm_constant uu____4904 ->
          let uu____4905 =
            let uu____4910 =
              let uu____4911 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4911
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4910)  in
          raise_err1 uu____4905
      | FStar_Syntax_Syntax.Tm_match uu____4912 ->
          let uu____4935 =
            let uu____4940 =
              let uu____4941 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4941
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4940)  in
          raise_err1 uu____4935
      | FStar_Syntax_Syntax.Tm_let uu____4942 ->
          let uu____4955 =
            let uu____4960 =
              let uu____4961 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4961
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4960)  in
          raise_err1 uu____4955
      | FStar_Syntax_Syntax.Tm_uvar uu____4962 ->
          let uu____4975 =
            let uu____4980 =
              let uu____4981 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4981
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4980)  in
          raise_err1 uu____4975
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4982 =
            let uu____4987 =
              let uu____4988 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4988
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4987)  in
          raise_err1 uu____4982
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4990 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4990
      | FStar_Syntax_Syntax.Tm_delayed uu____4993 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___336_5022  ->
    match uu___336_5022 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___335_5029  ->
                match uu___335_5029 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5030 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5036 =
      let uu____5037 = FStar_Syntax_Subst.compress t  in
      uu____5037.FStar_Syntax_Syntax.n  in
    match uu____5036 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5063 =
            let uu____5064 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5064  in
          is_C uu____5063  in
        if r
        then
          ((let uu____5080 =
              let uu____5081 =
                FStar_List.for_all
                  (fun uu____5089  ->
                     match uu____5089 with | (h,uu____5095) -> is_C h) args
                 in
              Prims.op_Negation uu____5081  in
            if uu____5080 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5099 =
              let uu____5100 =
                FStar_List.for_all
                  (fun uu____5109  ->
                     match uu____5109 with
                     | (h,uu____5115) ->
                         let uu____5116 = is_C h  in
                         Prims.op_Negation uu____5116) args
                 in
              Prims.op_Negation uu____5100  in
            if uu____5099 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5136 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5136 with
         | M t1 ->
             ((let uu____5139 = is_C t1  in
               if uu____5139 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5143) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5149) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5155,uu____5156) -> is_C t1
    | uu____5197 -> false
  
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
          let uu____5230 =
            let uu____5231 =
              let uu____5246 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____5249 =
                let uu____5258 =
                  let uu____5265 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____5265)  in
                [uu____5258]  in
              (uu____5246, uu____5249)  in
            FStar_Syntax_Syntax.Tm_app uu____5231  in
          mk1 uu____5230  in
        let uu____5290 =
          let uu____5291 = FStar_Syntax_Syntax.mk_binder p  in [uu____5291]
           in
        FStar_Syntax_Util.abs uu____5290 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___337_5308  ->
    match uu___337_5308 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5309 -> false
  
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
        let return_if uu____5544 =
          match uu____5544 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____5581 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____5583 =
                       let uu____5584 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____5584  in
                     Prims.op_Negation uu____5583)
                   in
                if uu____5581
                then
                  let uu____5585 =
                    let uu____5590 =
                      let uu____5591 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____5592 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____5593 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____5591 uu____5592 uu____5593
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____5590)  in
                  FStar_Errors.raise_error uu____5585
                    e.FStar_Syntax_Syntax.pos
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____5614 = mk_return env t1 s_e  in
                     ((M t1), uu____5614, u_e)))
               | (M t1,N t2) ->
                   let uu____5621 =
                     let uu____5626 =
                       let uu____5627 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____5628 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____5629 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____5627 uu____5628 uu____5629
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____5626)
                      in
                   FStar_Errors.raise_error uu____5621
                     e.FStar_Syntax_Syntax.pos)
           in
        let ensure_m env1 e2 =
          let strip_m uu___338_5678 =
            match uu___338_5678 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____5694 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____5714 =
                let uu____5719 =
                  let uu____5720 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____5720
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____5719)  in
              FStar_Errors.raise_error uu____5714 e2.FStar_Syntax_Syntax.pos
          | M uu____5727 ->
              let uu____5728 = check env1 e2 context_nm  in
              strip_m uu____5728
           in
        let uu____5735 =
          let uu____5736 = FStar_Syntax_Subst.compress e  in
          uu____5736.FStar_Syntax_Syntax.n  in
        match uu____5735 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5745 ->
            let uu____5746 = infer env e  in return_if uu____5746
        | FStar_Syntax_Syntax.Tm_name uu____5753 ->
            let uu____5754 = infer env e  in return_if uu____5754
        | FStar_Syntax_Syntax.Tm_fvar uu____5761 ->
            let uu____5762 = infer env e  in return_if uu____5762
        | FStar_Syntax_Syntax.Tm_abs uu____5769 ->
            let uu____5786 = infer env e  in return_if uu____5786
        | FStar_Syntax_Syntax.Tm_constant uu____5793 ->
            let uu____5794 = infer env e  in return_if uu____5794
        | FStar_Syntax_Syntax.Tm_quoted uu____5801 ->
            let uu____5808 = infer env e  in return_if uu____5808
        | FStar_Syntax_Syntax.Tm_app uu____5815 ->
            let uu____5830 = infer env e  in return_if uu____5830
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5838 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5838 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5900) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5906) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5912,uu____5913) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5954 ->
            let uu____5967 =
              let uu____5968 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5968  in
            failwith uu____5967
        | FStar_Syntax_Syntax.Tm_type uu____5975 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5982 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6001 ->
            let uu____6008 =
              let uu____6009 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6009  in
            failwith uu____6008
        | FStar_Syntax_Syntax.Tm_uvar uu____6016 ->
            let uu____6029 =
              let uu____6030 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6030  in
            failwith uu____6029
        | FStar_Syntax_Syntax.Tm_delayed uu____6037 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6066 =
              let uu____6067 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6067  in
            failwith uu____6066

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
      let raise_err1 msg =
        FStar_Errors.raise_error msg e.FStar_Syntax_Syntax.pos  in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env
         in
      let uu____6133 =
        let uu____6134 = FStar_Syntax_Subst.compress e  in
        uu____6134.FStar_Syntax_Syntax.n  in
      match uu____6133 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6152 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6152
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6199;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____6200;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6206 =
                  let uu___353_6207 = rc  in
                  let uu____6208 =
                    let uu____6213 =
                      let uu____6216 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____6216  in
                    FStar_Pervasives_Native.Some uu____6213  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___353_6207.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6208;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___353_6207.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____6206
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___354_6228 = env  in
            let uu____6229 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____6229;
              subst = (uu___354_6228.subst);
              tc_const = (uu___354_6228.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____6249  ->
                 match uu____6249 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___355_6262 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___355_6262.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___355_6262.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____6263 =
            FStar_List.fold_left
              (fun uu____6292  ->
                 fun uu____6293  ->
                   match (uu____6292, uu____6293) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____6341 = is_C c  in
                       if uu____6341
                       then
                         let xw =
                           let uu____6349 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____6349
                            in
                         let x =
                           let uu___356_6351 = bv  in
                           let uu____6352 =
                             let uu____6355 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____6355  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___356_6351.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___356_6351.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____6352
                           }  in
                         let env3 =
                           let uu___357_6357 = env2  in
                           let uu____6358 =
                             let uu____6361 =
                               let uu____6362 =
                                 let uu____6369 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____6369)  in
                               FStar_Syntax_Syntax.NT uu____6362  in
                             uu____6361 :: (env2.subst)  in
                           {
                             env = (uu___357_6357.env);
                             subst = uu____6358;
                             tc_const = (uu___357_6357.tc_const)
                           }  in
                         let uu____6374 =
                           let uu____6377 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____6378 =
                             let uu____6381 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____6381 :: acc  in
                           uu____6377 :: uu____6378  in
                         (env3, uu____6374)
                       else
                         (let x =
                            let uu___358_6386 = bv  in
                            let uu____6387 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___358_6386.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___358_6386.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____6387
                            }  in
                          let uu____6390 =
                            let uu____6393 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____6393 :: acc  in
                          (env2, uu____6390))) (env1, []) binders1
             in
          (match uu____6263 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____6413 =
                 let check_what =
                   let uu____6439 = is_monadic rc_opt1  in
                   if uu____6439 then check_m else check_n  in
                 let uu____6453 = check_what env2 body1  in
                 match uu____6453 with
                 | (t,s_body,u_body) ->
                     let uu____6473 =
                       let uu____6476 =
                         let uu____6477 = is_monadic rc_opt1  in
                         if uu____6477 then M t else N t  in
                       comp_of_nm uu____6476  in
                     (uu____6473, s_body, u_body)
                  in
               (match uu____6413 with
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
                                 let uu____6514 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___339_6518  ->
                                           match uu___339_6518 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____6519 -> false))
                                    in
                                 if uu____6514
                                 then
                                   let uu____6520 =
                                     FStar_List.filter
                                       (fun uu___340_6524  ->
                                          match uu___340_6524 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____6525 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____6520
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____6534 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___341_6538  ->
                                         match uu___341_6538 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____6539 -> false))
                                  in
                               if uu____6534
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___342_6546  ->
                                        match uu___342_6546 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____6547 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____6548 =
                                   let uu____6549 =
                                     let uu____6554 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____6554
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____6549 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____6548
                               else
                                 (let uu____6560 =
                                    let uu___359_6561 = rc  in
                                    let uu____6562 =
                                      let uu____6567 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____6567
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___359_6561.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____6562;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___359_6561.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____6560))
                       in
                    let uu____6572 =
                      let comp1 =
                        let uu____6580 = is_monadic rc_opt1  in
                        let uu____6581 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____6580 uu____6581
                         in
                      let uu____6582 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____6582,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____6572 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____6620 =
                             let uu____6621 =
                               let uu____6638 =
                                 let uu____6641 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____6641 s_rc_opt  in
                               (s_binders1, s_body1, uu____6638)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6621  in
                           mk1 uu____6620  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____6659 =
                             let uu____6660 =
                               let uu____6677 =
                                 let uu____6680 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____6680 u_rc_opt  in
                               (u_binders2, u_body2, uu____6677)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6660  in
                           mk1 uu____6659  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____6694;_};
            FStar_Syntax_Syntax.fv_delta = uu____6695;
            FStar_Syntax_Syntax.fv_qual = uu____6696;_}
          ->
          let uu____6699 =
            let uu____6704 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6704  in
          (match uu____6699 with
           | (uu____6735,t) ->
               let uu____6737 =
                 let uu____6738 = normalize1 t  in N uu____6738  in
               (uu____6737, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6739;
             FStar_Syntax_Syntax.vars = uu____6740;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6803 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6803 with
           | (unary_op,uu____6825) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6884;
             FStar_Syntax_Syntax.vars = uu____6885;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6961 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6961 with
           | (unary_op,uu____6983) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7048;
             FStar_Syntax_Syntax.vars = uu____7049;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____7079 = infer env a  in
          (match uu____7079 with
           | (t,s,u) ->
               let uu____7095 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7095 with
                | (head1,uu____7117) ->
                    let uu____7138 =
                      let uu____7139 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____7139  in
                    let uu____7140 =
                      let uu____7141 =
                        let uu____7142 =
                          let uu____7157 =
                            let uu____7166 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7166]  in
                          (head1, uu____7157)  in
                        FStar_Syntax_Syntax.Tm_app uu____7142  in
                      mk1 uu____7141  in
                    let uu____7195 =
                      let uu____7196 =
                        let uu____7197 =
                          let uu____7212 =
                            let uu____7221 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7221]  in
                          (head1, uu____7212)  in
                        FStar_Syntax_Syntax.Tm_app uu____7197  in
                      mk1 uu____7196  in
                    (uu____7138, uu____7140, uu____7195)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7250;
             FStar_Syntax_Syntax.vars = uu____7251;_},(a1,uu____7253)::a2::[])
          ->
          let uu____7295 = infer env a1  in
          (match uu____7295 with
           | (t,s,u) ->
               let uu____7311 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7311 with
                | (head1,uu____7333) ->
                    let uu____7354 =
                      let uu____7355 =
                        let uu____7356 =
                          let uu____7371 =
                            let uu____7380 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7380; a2]  in
                          (head1, uu____7371)  in
                        FStar_Syntax_Syntax.Tm_app uu____7356  in
                      mk1 uu____7355  in
                    let uu____7415 =
                      let uu____7416 =
                        let uu____7417 =
                          let uu____7432 =
                            let uu____7441 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7441; a2]  in
                          (head1, uu____7432)  in
                        FStar_Syntax_Syntax.Tm_app uu____7417  in
                      mk1 uu____7416  in
                    (t, uu____7354, uu____7415)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7476;
             FStar_Syntax_Syntax.vars = uu____7477;_},uu____7478)
          ->
          let uu____7499 =
            let uu____7504 =
              let uu____7505 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7505
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7504)  in
          FStar_Errors.raise_error uu____7499 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7512;
             FStar_Syntax_Syntax.vars = uu____7513;_},uu____7514)
          ->
          let uu____7535 =
            let uu____7540 =
              let uu____7541 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7541
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7540)  in
          FStar_Errors.raise_error uu____7535 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____7570 = check_n env head1  in
          (match uu____7570 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____7592 =
                   let uu____7593 = FStar_Syntax_Subst.compress t  in
                   uu____7593.FStar_Syntax_Syntax.n  in
                 match uu____7592 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____7596 -> true
                 | uu____7609 -> false  in
               let rec flatten1 t =
                 let uu____7628 =
                   let uu____7629 = FStar_Syntax_Subst.compress t  in
                   uu____7629.FStar_Syntax_Syntax.n  in
                 match uu____7628 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____7646);
                                FStar_Syntax_Syntax.pos = uu____7647;
                                FStar_Syntax_Syntax.vars = uu____7648;_})
                     when is_arrow t1 ->
                     let uu____7673 = flatten1 t1  in
                     (match uu____7673 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7755,uu____7756)
                     -> flatten1 e1
                 | uu____7797 ->
                     let uu____7798 =
                       let uu____7803 =
                         let uu____7804 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____7804
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____7803)  in
                     raise_err1 uu____7798
                  in
               let uu____7805 = flatten1 t_head  in
               (match uu____7805 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____7865 =
                          let uu____7870 =
                            let uu____7871 = FStar_Util.string_of_int n1  in
                            let uu____7878 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____7889 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____7871 uu____7878 uu____7889
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____7870)
                           in
                        FStar_Errors.raise_error uu____7865
                          e.FStar_Syntax_Syntax.pos)
                     else ();
                     (let uu____7897 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____7897 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____7946 args1 =
                            match uu____7946 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____8026 =
                                       let uu____8027 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____8027.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____8026
                                 | (binders3,[]) ->
                                     let uu____8057 =
                                       let uu____8058 =
                                         let uu____8061 =
                                           let uu____8062 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____8062
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____8061
                                          in
                                       uu____8058.FStar_Syntax_Syntax.n  in
                                     (match uu____8057 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____8089 =
                                            let uu____8090 =
                                              let uu____8091 =
                                                let uu____8104 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____8104)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____8091
                                               in
                                            mk1 uu____8090  in
                                          N uu____8089
                                      | uu____8115 -> failwith "wat?")
                                 | ([],uu____8116::uu____8117) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____8157)::binders3,(arg,uu____8160)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____8223 = FStar_List.splitAt n' binders1  in
                          (match uu____8223 with
                           | (binders2,uu____8255) ->
                               let uu____8280 =
                                 let uu____8299 =
                                   FStar_List.map2
                                     (fun uu____8349  ->
                                        fun uu____8350  ->
                                          match (uu____8349, uu____8350) with
                                          | ((bv,uu____8386),(arg,q)) ->
                                              let uu____8403 =
                                                let uu____8404 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____8404.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____8403 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____8421 ->
                                                   let uu____8422 =
                                                     let uu____8427 =
                                                       star_type' env arg  in
                                                     (uu____8427, q)  in
                                                   (uu____8422, [(arg, q)])
                                               | uu____8452 ->
                                                   let uu____8453 =
                                                     check_n env arg  in
                                                   (match uu____8453 with
                                                    | (uu____8474,s_arg,u_arg)
                                                        ->
                                                        let uu____8477 =
                                                          let uu____8484 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____8484
                                                          then
                                                            let uu____8491 =
                                                              let uu____8496
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____8496, q)
                                                               in
                                                            [uu____8491;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____8477))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____8299  in
                               (match uu____8280 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____8585 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____8596 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____8585, uu____8596)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____8660) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____8666) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8672,uu____8673) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____8715 = let uu____8716 = env.tc_const c  in N uu____8716
             in
          (uu____8715, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____8723 ->
          let uu____8736 =
            let uu____8737 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____8737  in
          failwith uu____8736
      | FStar_Syntax_Syntax.Tm_type uu____8744 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____8751 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____8770 ->
          let uu____8777 =
            let uu____8778 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____8778  in
          failwith uu____8777
      | FStar_Syntax_Syntax.Tm_uvar uu____8785 ->
          let uu____8798 =
            let uu____8799 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____8799  in
          failwith uu____8798
      | FStar_Syntax_Syntax.Tm_delayed uu____8806 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____8835 =
            let uu____8836 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8836  in
          failwith uu____8835

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
          let raise_err1 msg =
            FStar_Errors.raise_error msg e0.FStar_Syntax_Syntax.pos  in
          let uu____8945 = check_n env e0  in
          match uu____8945 with
          | (uu____8958,s_e0,u_e0) ->
              let uu____8961 =
                let uu____8990 =
                  FStar_List.map
                    (fun b  ->
                       let uu____9051 = FStar_Syntax_Subst.open_branch b  in
                       match uu____9051 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___360_9093 = env  in
                             let uu____9094 =
                               let uu____9095 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____9095
                                in
                             {
                               env = uu____9094;
                               subst = (uu___360_9093.subst);
                               tc_const = (uu___360_9093.tc_const)
                             }  in
                           let uu____9098 = f env1 body  in
                           (match uu____9098 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____9170 ->
                           raise_err1
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____8990  in
              (match uu____8961 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____9250 = FStar_List.hd nms  in
                     match uu____9250 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___343_9258  ->
                          match uu___343_9258 with
                          | M uu____9259 -> true
                          | uu____9260 -> false) nms
                      in
                   let uu____9261 =
                     let uu____9298 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____9388  ->
                              match uu____9388 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____9565 =
                                         check env original_body (M t2)  in
                                       (match uu____9565 with
                                        | (uu____9602,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____9641,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____9298  in
                   (match uu____9261 with
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
                              (fun uu____9825  ->
                                 match uu____9825 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____9876 =
                                         let uu____9877 =
                                           let uu____9892 =
                                             let uu____9901 =
                                               let uu____9908 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____9911 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____9908, uu____9911)  in
                                             [uu____9901]  in
                                           (s_body, uu____9892)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____9877
                                          in
                                       mk1 uu____9876  in
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
                            let uu____10035 =
                              let uu____10036 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10036]  in
                            let uu____10049 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____10035 uu____10049
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____10073 =
                              let uu____10080 =
                                let uu____10085 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____10085
                                 in
                              [uu____10080]  in
                            let uu____10098 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____10073 uu____10098
                             in
                          let uu____10101 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____10140 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____10101, uu____10140)
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
                           let uu____10249 =
                             let uu____10250 =
                               let uu____10251 =
                                 let uu____10278 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____10278,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10251
                                in
                             mk1 uu____10250  in
                           let uu____10337 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____10249, uu____10337))))

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
              let uu____10400 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10400]  in
            let uu____10413 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____10413 with
            | (x_binders1,e21) ->
                let uu____10426 = infer env e1  in
                (match uu____10426 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____10443 = is_C t1  in
                       if uu____10443
                       then
                         let uu___361_10444 = binding  in
                         let uu____10445 =
                           let uu____10448 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____10448  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___361_10444.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___361_10444.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____10445;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___361_10444.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___361_10444.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___361_10444.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___361_10444.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___362_10451 = env  in
                       let uu____10452 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___363_10454 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___363_10454.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___363_10454.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10452;
                         subst = (uu___362_10451.subst);
                         tc_const = (uu___362_10451.tc_const)
                       }  in
                     let uu____10455 = proceed env1 e21  in
                     (match uu____10455 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___364_10472 = binding  in
                            let uu____10473 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___364_10472.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___364_10472.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____10473;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___364_10472.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___364_10472.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___364_10472.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___364_10472.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____10476 =
                            let uu____10477 =
                              let uu____10478 =
                                let uu____10491 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___365_10505 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___365_10505.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___365_10505.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___365_10505.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___365_10505.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___365_10505.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___365_10505.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10491)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10478  in
                            mk1 uu____10477  in
                          let uu____10506 =
                            let uu____10507 =
                              let uu____10508 =
                                let uu____10521 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___366_10535 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___366_10535.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___366_10535.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___366_10535.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___366_10535.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___366_10535.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___366_10535.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10521)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10508  in
                            mk1 uu____10507  in
                          (nm_rec, uu____10476, uu____10506))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___367_10540 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___367_10540.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___367_10540.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___367_10540.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___367_10540.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___367_10540.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___368_10542 = env  in
                       let uu____10543 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___369_10545 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___369_10545.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___369_10545.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10543;
                         subst = (uu___368_10542.subst);
                         tc_const = (uu___368_10542.tc_const)
                       }  in
                     let uu____10546 = ensure_m env1 e21  in
                     (match uu____10546 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____10569 =
                              let uu____10570 =
                                let uu____10585 =
                                  let uu____10594 =
                                    let uu____10601 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____10604 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____10601, uu____10604)  in
                                  [uu____10594]  in
                                (s_e2, uu____10585)  in
                              FStar_Syntax_Syntax.Tm_app uu____10570  in
                            mk1 uu____10569  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____10635 =
                              let uu____10636 =
                                let uu____10651 =
                                  let uu____10660 =
                                    let uu____10667 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____10667)  in
                                  [uu____10660]  in
                                (s_e1, uu____10651)  in
                              FStar_Syntax_Syntax.Tm_app uu____10636  in
                            mk1 uu____10635  in
                          let uu____10692 =
                            let uu____10693 =
                              let uu____10694 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10694]  in
                            FStar_Syntax_Util.abs uu____10693 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____10707 =
                            let uu____10708 =
                              let uu____10709 =
                                let uu____10722 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___370_10736 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___370_10736.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___370_10736.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___370_10736.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___370_10736.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___370_10736.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___370_10736.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10722)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10709  in
                            mk1 uu____10708  in
                          ((M t2), uu____10692, uu____10707)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10746 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____10746  in
      let uu____10747 = check env e mn  in
      match uu____10747 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10763 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10785 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____10785  in
      let uu____10786 = check env e mn  in
      match uu____10786 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10802 -> failwith "[check_m]: impossible"

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
        (let uu____10832 =
           let uu____10833 = is_C c  in Prims.op_Negation uu____10833  in
         if uu____10832 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____10843 =
           let uu____10844 = FStar_Syntax_Subst.compress c  in
           uu____10844.FStar_Syntax_Syntax.n  in
         match uu____10843 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____10869 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____10869 with
              | (wp_head,wp_args) ->
                  ((let uu____10907 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____10921 =
                           let uu____10922 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____10922
                            in
                         Prims.op_Negation uu____10921)
                       in
                    if uu____10907 then failwith "mismatch" else ());
                   (let uu____10930 =
                      let uu____10931 =
                        let uu____10946 =
                          FStar_List.map2
                            (fun uu____10976  ->
                               fun uu____10977  ->
                                 match (uu____10976, uu____10977) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____11016 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____11016
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____11019 =
                                           let uu____11024 =
                                             let uu____11025 =
                                               print_implicit q  in
                                             let uu____11026 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____11025 uu____11026
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____11024)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____11019)
                                      else ();
                                      (let uu____11028 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____11028, q)))) args wp_args
                           in
                        (head1, uu____10946)  in
                      FStar_Syntax_Syntax.Tm_app uu____10931  in
                    mk1 uu____10930)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____11064 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____11064 with
              | (binders_orig,comp1) ->
                  let uu____11071 =
                    let uu____11086 =
                      FStar_List.map
                        (fun uu____11120  ->
                           match uu____11120 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____11140 = is_C h  in
                               if uu____11140
                               then
                                 let w' =
                                   let uu____11152 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____11152
                                    in
                                 let uu____11153 =
                                   let uu____11160 =
                                     let uu____11167 =
                                       let uu____11172 =
                                         let uu____11173 =
                                           let uu____11174 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____11174  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____11173
                                          in
                                       (uu____11172, q)  in
                                     [uu____11167]  in
                                   (w', q) :: uu____11160  in
                                 (w', uu____11153)
                               else
                                 (let x =
                                    let uu____11195 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____11195
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____11086  in
                  (match uu____11071 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____11250 =
                           let uu____11253 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____11253
                            in
                         FStar_Syntax_Subst.subst_comp uu____11250 comp1  in
                       let app =
                         let uu____11257 =
                           let uu____11258 =
                             let uu____11273 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____11290 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____11291 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____11290, uu____11291)) bvs
                                in
                             (wp, uu____11273)  in
                           FStar_Syntax_Syntax.Tm_app uu____11258  in
                         mk1 uu____11257  in
                       let comp3 =
                         let uu____11303 = type_of_comp comp2  in
                         let uu____11304 = is_monadic_comp comp2  in
                         trans_G env uu____11303 uu____11304 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____11306,uu____11307) ->
             trans_F_ env e wp
         | uu____11348 -> failwith "impossible trans_F_")

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
            let uu____11353 =
              let uu____11354 = star_type' env h  in
              let uu____11357 =
                let uu____11366 =
                  let uu____11373 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____11373)  in
                [uu____11366]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____11354;
                FStar_Syntax_Syntax.effect_args = uu____11357;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____11353
          else
            (let uu____11389 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____11389)

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
    fun t  -> let uu____11408 = n env.env t  in star_type' env uu____11408
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____11427 = n env.env t  in check_n env uu____11427
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____11443 = n env.env c  in
        let uu____11444 = n env.env wp  in
        trans_F_ env uu____11443 uu____11444
  