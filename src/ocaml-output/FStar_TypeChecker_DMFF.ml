open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }[@@deriving show]
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
              let uu___105_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___105_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___105_123.FStar_Syntax_Syntax.index);
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
                          let uu___106_2608 = t1  in
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
                              (uu___106_2608.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___106_2608.FStar_Syntax_Syntax.vars)
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
                      let uu____2695 =
                        let uu____2696 = FStar_Syntax_Subst.compress t1  in
                        uu____2696.FStar_Syntax_Syntax.n  in
                      match uu____2695 with
                      | FStar_Syntax_Syntax.Tm_type uu____2701 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2724 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2724
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2743 =
                                let uu____2744 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2744 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2743
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2765 =
                            let uu____2776 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2796  ->
                                     match uu____2796 with
                                     | (t2,q) ->
                                         let uu____2811 = project i x  in
                                         let uu____2814 = project i y  in
                                         mk_stronger t2 uu____2811 uu____2814)
                                args
                               in
                            match uu____2776 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2765 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2877);
                                      FStar_Syntax_Syntax.pos = uu____2878;
                                      FStar_Syntax_Syntax.vars = uu____2879;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2917  ->
                                   match uu____2917 with
                                   | (bv,q) ->
                                       let uu____2924 =
                                         let uu____2925 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2925  in
                                       FStar_Syntax_Syntax.gen_bv uu____2924
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2932 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2932) bvs
                             in
                          let body =
                            let uu____2936 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2939 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2936 uu____2939  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2948);
                                      FStar_Syntax_Syntax.pos = uu____2949;
                                      FStar_Syntax_Syntax.vars = uu____2950;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2988  ->
                                   match uu____2988 with
                                   | (bv,q) ->
                                       let uu____2995 =
                                         let uu____2996 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2996  in
                                       FStar_Syntax_Syntax.gen_bv uu____2995
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____3003 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____3003) bvs
                             in
                          let body =
                            let uu____3007 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____3010 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____3007 uu____3010  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____3017 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____3023 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____3026 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____3029 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____3023 uu____3026 uu____3029  in
                    let uu____3032 =
                      let uu____3033 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____3033  in
                    FStar_Syntax_Util.abs uu____3032 body ret_tot_type  in
                  let stronger1 =
                    let uu____3061 = mk_lid "stronger"  in
                    register env1 uu____3061 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3069 = FStar_Util.prefix gamma  in
                    match uu____3069 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3118 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3118
                             in
                          let uu____3121 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3121 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3129 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3129  in
                              let guard_free1 =
                                let uu____3139 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3139  in
                              let pat =
                                let uu____3143 =
                                  let uu____3152 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3152]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3143
                                 in
                              let pattern_guarded_body =
                                let uu____3174 =
                                  let uu____3175 =
                                    let uu____3182 =
                                      let uu____3183 =
                                        let uu____3194 =
                                          let uu____3203 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3203]  in
                                        [uu____3194]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3183
                                       in
                                    (body, uu____3182)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3175  in
                                mk1 uu____3174  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3240 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3246 =
                            let uu____3249 =
                              let uu____3250 =
                                let uu____3253 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3256 =
                                  let uu____3265 = args_of_binders1 wp_args
                                     in
                                  let uu____3268 =
                                    let uu____3271 =
                                      let uu____3272 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3272
                                       in
                                    [uu____3271]  in
                                  FStar_List.append uu____3265 uu____3268  in
                                FStar_Syntax_Util.mk_app uu____3253
                                  uu____3256
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3250  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3249
                             in
                          FStar_Syntax_Util.abs gamma uu____3246
                            ret_gtot_type
                           in
                        let uu____3273 =
                          let uu____3274 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3274  in
                        FStar_Syntax_Util.abs uu____3273 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3286 = mk_lid "wp_ite"  in
                    register env1 uu____3286 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3294 = FStar_Util.prefix gamma  in
                    match uu____3294 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3339 =
                            let uu____3340 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3345 =
                              let uu____3354 =
                                let uu____3361 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3361  in
                              [uu____3354]  in
                            FStar_Syntax_Util.mk_app uu____3340 uu____3345
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3339
                           in
                        let uu____3374 =
                          let uu____3375 =
                            let uu____3382 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3382 gamma  in
                          FStar_List.append binders uu____3375  in
                        FStar_Syntax_Util.abs uu____3374 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3398 = mk_lid "null_wp"  in
                    register env1 uu____3398 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3409 =
                        let uu____3418 =
                          let uu____3421 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3422 =
                            let uu____3425 =
                              let uu____3426 =
                                let uu____3435 =
                                  let uu____3442 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3442  in
                                [uu____3435]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3426
                               in
                            let uu____3455 =
                              let uu____3458 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3458]  in
                            uu____3425 :: uu____3455  in
                          uu____3421 :: uu____3422  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3418
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3409  in
                    let uu____3465 =
                      let uu____3466 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3466  in
                    FStar_Syntax_Util.abs uu____3465 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3478 = mk_lid "wp_trivial"  in
                    register env1 uu____3478 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3483 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3483
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____3490 =
                      let uu____3491 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____3491  in
                    let uu____3543 =
                      let uu___107_3544 = ed  in
                      let uu____3545 =
                        let uu____3546 = c wp_if_then_else2  in
                        ([], uu____3546)  in
                      let uu____3553 =
                        let uu____3554 = c wp_ite2  in ([], uu____3554)  in
                      let uu____3561 =
                        let uu____3562 = c stronger2  in ([], uu____3562)  in
                      let uu____3569 =
                        let uu____3570 = c wp_close2  in ([], uu____3570)  in
                      let uu____3577 =
                        let uu____3578 = c wp_assert2  in ([], uu____3578)
                         in
                      let uu____3585 =
                        let uu____3586 = c wp_assume2  in ([], uu____3586)
                         in
                      let uu____3593 =
                        let uu____3594 = c null_wp2  in ([], uu____3594)  in
                      let uu____3601 =
                        let uu____3602 = c wp_trivial2  in ([], uu____3602)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___107_3544.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___107_3544.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___107_3544.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___107_3544.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___107_3544.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___107_3544.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___107_3544.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3545;
                        FStar_Syntax_Syntax.ite_wp = uu____3553;
                        FStar_Syntax_Syntax.stronger = uu____3561;
                        FStar_Syntax_Syntax.close_wp = uu____3569;
                        FStar_Syntax_Syntax.assert_p = uu____3577;
                        FStar_Syntax_Syntax.assume_p = uu____3585;
                        FStar_Syntax_Syntax.null_wp = uu____3593;
                        FStar_Syntax_Syntax.trivial = uu____3601;
                        FStar_Syntax_Syntax.repr =
                          (uu___107_3544.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___107_3544.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___107_3544.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___107_3544.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___107_3544.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____3490, uu____3543)))))
  
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___108_3624 = dmff_env  in
      {
        env = env';
        subst = (uu___108_3624.subst);
        tc_const = (uu___108_3624.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____3641 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____3655 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___94_3667  ->
    match uu___94_3667 with
    | FStar_Syntax_Syntax.Total (t,uu____3669) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___93_3682  ->
                match uu___93_3682 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3683 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____3685 =
          let uu____3686 =
            let uu____3687 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3687
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3686  in
        failwith uu____3685
    | FStar_Syntax_Syntax.GTotal uu____3688 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___95_3701  ->
    match uu___95_3701 with
    | N t ->
        let uu____3703 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____3703
    | M t ->
        let uu____3705 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____3705
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3711,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____3713;
                      FStar_Syntax_Syntax.vars = uu____3714;_})
        -> nm_of_comp n2
    | uu____3731 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____3741 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3741 with | M uu____3742 -> true | N uu____3743 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3749 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3763 =
        let uu____3770 =
          let uu____3775 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3775  in
        [uu____3770]  in
      let uu____3788 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3763 uu____3788  in
    let uu____3791 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3791
  
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
        let uu____3834 =
          let uu____3835 =
            let uu____3848 =
              let uu____3855 =
                let uu____3860 =
                  let uu____3861 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____3861  in
                let uu____3862 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____3860, uu____3862)  in
              [uu____3855]  in
            let uu____3871 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____3848, uu____3871)  in
          FStar_Syntax_Syntax.Tm_arrow uu____3835  in
        mk1 uu____3834

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3909) ->
          let binders1 =
            FStar_List.map
              (fun uu____3945  ->
                 match uu____3945 with
                 | (bv,aqual) ->
                     let uu____3956 =
                       let uu___109_3957 = bv  in
                       let uu____3958 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___109_3957.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___109_3957.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3958
                       }  in
                     (uu____3956, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3961,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3963);
                             FStar_Syntax_Syntax.pos = uu____3964;
                             FStar_Syntax_Syntax.vars = uu____3965;_})
               ->
               let uu____3990 =
                 let uu____3991 =
                   let uu____4004 =
                     let uu____4007 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____4007  in
                   (binders1, uu____4004)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3991  in
               mk1 uu____3990
           | uu____4016 ->
               let uu____4017 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____4017 with
                | N hn ->
                    let uu____4019 =
                      let uu____4020 =
                        let uu____4033 =
                          let uu____4036 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____4036  in
                        (binders1, uu____4033)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4020  in
                    mk1 uu____4019
                | M a ->
                    let uu____4046 =
                      let uu____4047 =
                        let uu____4060 =
                          let uu____4067 =
                            let uu____4074 =
                              let uu____4079 =
                                let uu____4080 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4080  in
                              let uu____4081 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4079, uu____4081)  in
                            [uu____4074]  in
                          FStar_List.append binders1 uu____4067  in
                        let uu____4094 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4060, uu____4094)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4047  in
                    mk1 uu____4046))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4176 = f x  in
                    FStar_Util.string_builder_append strb uu____4176);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4183 = f x1  in
                         FStar_Util.string_builder_append strb uu____4183))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4185 =
              let uu____4190 =
                let uu____4191 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4192 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4191 uu____4192
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4190)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4185  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4208 =
              let uu____4209 = FStar_Syntax_Subst.compress ty  in
              uu____4209.FStar_Syntax_Syntax.n  in
            match uu____4208 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4230 =
                  let uu____4231 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4231  in
                if uu____4230
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____4265 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____4265 s  in
                       let uu____4268 =
                         let uu____4269 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____4269  in
                       if uu____4268
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____4272 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____4272 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____4294  ->
                                  match uu____4294 with
                                  | (bv,uu____4304) ->
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
            | uu____4318 ->
                ((let uu____4320 =
                    let uu____4325 =
                      let uu____4326 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4326
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4325)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4320);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4337 =
              let uu____4338 = FStar_Syntax_Subst.compress head2  in
              uu____4338.FStar_Syntax_Syntax.n  in
            match uu____4337 with
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
                  (let uu____4343 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4343)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4345 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4345 with
                 | ((uu____4354,ty),uu____4356) ->
                     let uu____4361 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4361
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.env t1
                          in
                       let uu____4369 =
                         let uu____4370 = FStar_Syntax_Subst.compress res  in
                         uu____4370.FStar_Syntax_Syntax.n  in
                       (match uu____4369 with
                        | FStar_Syntax_Syntax.Tm_app uu____4373 -> true
                        | uu____4388 ->
                            ((let uu____4390 =
                                let uu____4395 =
                                  let uu____4396 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____4396
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____4395)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____4390);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____4398 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4399 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4401) ->
                is_valid_application t2
            | uu____4406 -> false  in
          let uu____4407 = is_valid_application head1  in
          if uu____4407
          then
            let uu____4408 =
              let uu____4409 =
                let uu____4424 =
                  FStar_List.map
                    (fun uu____4447  ->
                       match uu____4447 with
                       | (t2,qual) ->
                           let uu____4464 = star_type' env t2  in
                           (uu____4464, qual)) args
                   in
                (head1, uu____4424)  in
              FStar_Syntax_Syntax.Tm_app uu____4409  in
            mk1 uu____4408
          else
            (let uu____4476 =
               let uu____4481 =
                 let uu____4482 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____4482
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____4481)  in
             FStar_Errors.raise_err uu____4476)
      | FStar_Syntax_Syntax.Tm_bvar uu____4483 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____4484 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____4485 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____4486 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____4510 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____4510 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___112_4518 = env  in
                 let uu____4519 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____4519;
                   subst = (uu___112_4518.subst);
                   tc_const = (uu___112_4518.tc_const)
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
               ((let uu___113_4541 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___113_4541.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___113_4541.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____4548 =
            let uu____4549 =
              let uu____4556 = star_type' env t2  in (uu____4556, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____4549  in
          mk1 uu____4548
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____4608 =
            let uu____4609 =
              let uu____4636 = star_type' env e  in
              let uu____4639 =
                let uu____4656 =
                  let uu____4665 = star_type' env t2  in
                  FStar_Util.Inl uu____4665  in
                (uu____4656, FStar_Pervasives_Native.None)  in
              (uu____4636, uu____4639, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4609  in
          mk1 uu____4608
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____4753 =
            let uu____4754 =
              let uu____4781 = star_type' env e  in
              let uu____4784 =
                let uu____4801 =
                  let uu____4810 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4810  in
                (uu____4801, FStar_Pervasives_Native.None)  in
              (uu____4781, uu____4784, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4754  in
          mk1 uu____4753
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4851,(uu____4852,FStar_Pervasives_Native.Some uu____4853),uu____4854)
          ->
          let uu____4903 =
            let uu____4908 =
              let uu____4909 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4909
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4908)  in
          FStar_Errors.raise_err uu____4903
      | FStar_Syntax_Syntax.Tm_refine uu____4910 ->
          let uu____4917 =
            let uu____4922 =
              let uu____4923 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4923
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4922)  in
          FStar_Errors.raise_err uu____4917
      | FStar_Syntax_Syntax.Tm_uinst uu____4924 ->
          let uu____4931 =
            let uu____4936 =
              let uu____4937 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4937
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4936)  in
          FStar_Errors.raise_err uu____4931
      | FStar_Syntax_Syntax.Tm_quoted uu____4938 ->
          let uu____4945 =
            let uu____4950 =
              let uu____4951 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4951
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4950)  in
          FStar_Errors.raise_err uu____4945
      | FStar_Syntax_Syntax.Tm_constant uu____4952 ->
          let uu____4953 =
            let uu____4958 =
              let uu____4959 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4959
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4958)  in
          FStar_Errors.raise_err uu____4953
      | FStar_Syntax_Syntax.Tm_match uu____4960 ->
          let uu____4983 =
            let uu____4988 =
              let uu____4989 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4989
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4988)  in
          FStar_Errors.raise_err uu____4983
      | FStar_Syntax_Syntax.Tm_let uu____4990 ->
          let uu____5003 =
            let uu____5008 =
              let uu____5009 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5009
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5008)  in
          FStar_Errors.raise_err uu____5003
      | FStar_Syntax_Syntax.Tm_uvar uu____5010 ->
          let uu____5017 =
            let uu____5022 =
              let uu____5023 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5023
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5022)  in
          FStar_Errors.raise_err uu____5017
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5024 =
            let uu____5029 =
              let uu____5030 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5030
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5029)  in
          FStar_Errors.raise_err uu____5024
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5032 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____5032
      | FStar_Syntax_Syntax.Tm_delayed uu____5035 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___97_5066  ->
    match uu___97_5066 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___96_5073  ->
                match uu___96_5073 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5074 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5080 =
      let uu____5081 = FStar_Syntax_Subst.compress t  in
      uu____5081.FStar_Syntax_Syntax.n  in
    match uu____5080 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5107 =
            let uu____5108 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5108  in
          is_C uu____5107  in
        if r
        then
          ((let uu____5124 =
              let uu____5125 =
                FStar_List.for_all
                  (fun uu____5133  ->
                     match uu____5133 with | (h,uu____5139) -> is_C h) args
                 in
              Prims.op_Negation uu____5125  in
            if uu____5124 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5143 =
              let uu____5144 =
                FStar_List.for_all
                  (fun uu____5153  ->
                     match uu____5153 with
                     | (h,uu____5159) ->
                         let uu____5160 = is_C h  in
                         Prims.op_Negation uu____5160) args
                 in
              Prims.op_Negation uu____5144  in
            if uu____5143 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5180 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5180 with
         | M t1 ->
             ((let uu____5183 = is_C t1  in
               if uu____5183 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5187) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5193) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5199,uu____5200) -> is_C t1
    | uu____5241 -> false
  
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
          let uu____5274 =
            let uu____5275 =
              let uu____5290 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____5293 =
                let uu____5302 =
                  let uu____5309 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____5309)  in
                [uu____5302]  in
              (uu____5290, uu____5293)  in
            FStar_Syntax_Syntax.Tm_app uu____5275  in
          mk1 uu____5274  in
        let uu____5334 =
          let uu____5335 = FStar_Syntax_Syntax.mk_binder p  in [uu____5335]
           in
        FStar_Syntax_Util.abs uu____5334 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___98_5352  ->
    match uu___98_5352 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5353 -> false
  
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
        let return_if uu____5588 =
          match uu____5588 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____5625 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____5627 =
                       let uu____5628 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____5628  in
                     Prims.op_Negation uu____5627)
                   in
                if uu____5625
                then
                  let uu____5629 =
                    let uu____5634 =
                      let uu____5635 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____5636 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____5637 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____5635 uu____5636 uu____5637
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____5634)  in
                  FStar_Errors.raise_err uu____5629
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____5660 = mk_return env t1 s_e  in
                     ((M t1), uu____5660, u_e)))
               | (M t1,N t2) ->
                   let uu____5667 =
                     let uu____5672 =
                       let uu____5673 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____5674 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____5675 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____5673 uu____5674 uu____5675
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____5672)
                      in
                   FStar_Errors.raise_err uu____5667)
           in
        let ensure_m env1 e2 =
          let strip_m uu___99_5724 =
            match uu___99_5724 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____5740 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____5760 =
                let uu____5765 =
                  let uu____5766 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____5766
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____5765)  in
              FStar_Errors.raise_error uu____5760 e2.FStar_Syntax_Syntax.pos
          | M uu____5773 ->
              let uu____5774 = check env1 e2 context_nm  in
              strip_m uu____5774
           in
        let uu____5781 =
          let uu____5782 = FStar_Syntax_Subst.compress e  in
          uu____5782.FStar_Syntax_Syntax.n  in
        match uu____5781 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5791 ->
            let uu____5792 = infer env e  in return_if uu____5792
        | FStar_Syntax_Syntax.Tm_name uu____5799 ->
            let uu____5800 = infer env e  in return_if uu____5800
        | FStar_Syntax_Syntax.Tm_fvar uu____5807 ->
            let uu____5808 = infer env e  in return_if uu____5808
        | FStar_Syntax_Syntax.Tm_abs uu____5815 ->
            let uu____5832 = infer env e  in return_if uu____5832
        | FStar_Syntax_Syntax.Tm_constant uu____5839 ->
            let uu____5840 = infer env e  in return_if uu____5840
        | FStar_Syntax_Syntax.Tm_quoted uu____5847 ->
            let uu____5854 = infer env e  in return_if uu____5854
        | FStar_Syntax_Syntax.Tm_app uu____5861 ->
            let uu____5876 = infer env e  in return_if uu____5876
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5884 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5884 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5946) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5952) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5958,uu____5959) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6000 ->
            let uu____6013 =
              let uu____6014 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6014  in
            failwith uu____6013
        | FStar_Syntax_Syntax.Tm_type uu____6021 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6028 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6047 ->
            let uu____6054 =
              let uu____6055 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6055  in
            failwith uu____6054
        | FStar_Syntax_Syntax.Tm_uvar uu____6062 ->
            let uu____6069 =
              let uu____6070 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6070  in
            failwith uu____6069
        | FStar_Syntax_Syntax.Tm_delayed uu____6077 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6108 =
              let uu____6109 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6109  in
            failwith uu____6108

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
      let uu____6137 =
        let uu____6138 = FStar_Syntax_Subst.compress e  in
        uu____6138.FStar_Syntax_Syntax.n  in
      match uu____6137 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6156 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6156
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6203;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____6204;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6210 =
                  let uu___114_6211 = rc  in
                  let uu____6212 =
                    let uu____6217 =
                      let uu____6220 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____6220  in
                    FStar_Pervasives_Native.Some uu____6217  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___114_6211.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6212;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___114_6211.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____6210
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___115_6232 = env  in
            let uu____6233 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____6233;
              subst = (uu___115_6232.subst);
              tc_const = (uu___115_6232.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____6253  ->
                 match uu____6253 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___116_6266 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___116_6266.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___116_6266.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____6267 =
            FStar_List.fold_left
              (fun uu____6296  ->
                 fun uu____6297  ->
                   match (uu____6296, uu____6297) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____6345 = is_C c  in
                       if uu____6345
                       then
                         let xw =
                           let uu____6353 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____6353
                            in
                         let x =
                           let uu___117_6355 = bv  in
                           let uu____6356 =
                             let uu____6359 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____6359  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___117_6355.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___117_6355.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____6356
                           }  in
                         let env3 =
                           let uu___118_6361 = env2  in
                           let uu____6362 =
                             let uu____6365 =
                               let uu____6366 =
                                 let uu____6373 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____6373)  in
                               FStar_Syntax_Syntax.NT uu____6366  in
                             uu____6365 :: (env2.subst)  in
                           {
                             env = (uu___118_6361.env);
                             subst = uu____6362;
                             tc_const = (uu___118_6361.tc_const)
                           }  in
                         let uu____6378 =
                           let uu____6381 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____6382 =
                             let uu____6385 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____6385 :: acc  in
                           uu____6381 :: uu____6382  in
                         (env3, uu____6378)
                       else
                         (let x =
                            let uu___119_6390 = bv  in
                            let uu____6391 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_6390.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_6390.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____6391
                            }  in
                          let uu____6394 =
                            let uu____6397 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____6397 :: acc  in
                          (env2, uu____6394))) (env1, []) binders1
             in
          (match uu____6267 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____6417 =
                 let check_what =
                   let uu____6441 = is_monadic rc_opt1  in
                   if uu____6441 then check_m else check_n  in
                 let uu____6455 = check_what env2 body1  in
                 match uu____6455 with
                 | (t,s_body,u_body) ->
                     let uu____6473 =
                       let uu____6474 =
                         let uu____6475 = is_monadic rc_opt1  in
                         if uu____6475 then M t else N t  in
                       comp_of_nm uu____6474  in
                     (uu____6473, s_body, u_body)
                  in
               (match uu____6417 with
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
                                 let uu____6506 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___100_6510  ->
                                           match uu___100_6510 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____6511 -> false))
                                    in
                                 if uu____6506
                                 then
                                   let uu____6512 =
                                     FStar_List.filter
                                       (fun uu___101_6516  ->
                                          match uu___101_6516 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____6517 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____6512
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____6526 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___102_6530  ->
                                         match uu___102_6530 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____6531 -> false))
                                  in
                               if uu____6526
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___103_6538  ->
                                        match uu___103_6538 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____6539 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____6540 =
                                   let uu____6541 =
                                     let uu____6546 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____6546
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____6541 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____6540
                               else
                                 (let uu____6552 =
                                    let uu___120_6553 = rc  in
                                    let uu____6554 =
                                      let uu____6559 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____6559
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___120_6553.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____6554;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___120_6553.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____6552))
                       in
                    let uu____6564 =
                      let comp1 =
                        let uu____6574 = is_monadic rc_opt1  in
                        let uu____6575 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____6574 uu____6575
                         in
                      let uu____6576 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____6576,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____6564 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____6622 =
                             let uu____6623 =
                               let uu____6640 =
                                 let uu____6643 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____6643 s_rc_opt  in
                               (s_binders1, s_body1, uu____6640)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6623  in
                           mk1 uu____6622  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____6661 =
                             let uu____6662 =
                               let uu____6679 =
                                 let uu____6682 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____6682 u_rc_opt  in
                               (u_binders2, u_body2, uu____6679)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6662  in
                           mk1 uu____6661  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____6696;_};
            FStar_Syntax_Syntax.fv_delta = uu____6697;
            FStar_Syntax_Syntax.fv_qual = uu____6698;_}
          ->
          let uu____6701 =
            let uu____6706 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6706  in
          (match uu____6701 with
           | (uu____6737,t) ->
               let uu____6739 =
                 let uu____6740 = normalize1 t  in N uu____6740  in
               (uu____6739, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6741;
             FStar_Syntax_Syntax.vars = uu____6742;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6805 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6805 with
           | (unary_op,uu____6827) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6886;
             FStar_Syntax_Syntax.vars = uu____6887;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6963 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6963 with
           | (unary_op,uu____6985) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7050;
             FStar_Syntax_Syntax.vars = uu____7051;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____7081 = infer env a  in
          (match uu____7081 with
           | (t,s,u) ->
               let uu____7097 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7097 with
                | (head1,uu____7119) ->
                    let uu____7140 =
                      let uu____7141 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____7141  in
                    let uu____7142 =
                      let uu____7143 =
                        let uu____7144 =
                          let uu____7159 =
                            let uu____7168 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7168]  in
                          (head1, uu____7159)  in
                        FStar_Syntax_Syntax.Tm_app uu____7144  in
                      mk1 uu____7143  in
                    let uu____7197 =
                      let uu____7198 =
                        let uu____7199 =
                          let uu____7214 =
                            let uu____7223 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7223]  in
                          (head1, uu____7214)  in
                        FStar_Syntax_Syntax.Tm_app uu____7199  in
                      mk1 uu____7198  in
                    (uu____7140, uu____7142, uu____7197)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7252;
             FStar_Syntax_Syntax.vars = uu____7253;_},(a1,uu____7255)::a2::[])
          ->
          let uu____7297 = infer env a1  in
          (match uu____7297 with
           | (t,s,u) ->
               let uu____7313 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7313 with
                | (head1,uu____7335) ->
                    let uu____7356 =
                      let uu____7357 =
                        let uu____7358 =
                          let uu____7373 =
                            let uu____7382 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7382; a2]  in
                          (head1, uu____7373)  in
                        FStar_Syntax_Syntax.Tm_app uu____7358  in
                      mk1 uu____7357  in
                    let uu____7417 =
                      let uu____7418 =
                        let uu____7419 =
                          let uu____7434 =
                            let uu____7443 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7443; a2]  in
                          (head1, uu____7434)  in
                        FStar_Syntax_Syntax.Tm_app uu____7419  in
                      mk1 uu____7418  in
                    (t, uu____7356, uu____7417)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7478;
             FStar_Syntax_Syntax.vars = uu____7479;_},uu____7480)
          ->
          let uu____7501 =
            let uu____7506 =
              let uu____7507 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7507
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7506)  in
          FStar_Errors.raise_error uu____7501 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7514;
             FStar_Syntax_Syntax.vars = uu____7515;_},uu____7516)
          ->
          let uu____7537 =
            let uu____7542 =
              let uu____7543 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7543
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7542)  in
          FStar_Errors.raise_error uu____7537 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____7572 = check_n env head1  in
          (match uu____7572 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____7594 =
                   let uu____7595 = FStar_Syntax_Subst.compress t  in
                   uu____7595.FStar_Syntax_Syntax.n  in
                 match uu____7594 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____7598 -> true
                 | uu____7611 -> false  in
               let rec flatten1 t =
                 let uu____7630 =
                   let uu____7631 = FStar_Syntax_Subst.compress t  in
                   uu____7631.FStar_Syntax_Syntax.n  in
                 match uu____7630 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____7648);
                                FStar_Syntax_Syntax.pos = uu____7649;
                                FStar_Syntax_Syntax.vars = uu____7650;_})
                     when is_arrow t1 ->
                     let uu____7675 = flatten1 t1  in
                     (match uu____7675 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7757,uu____7758)
                     -> flatten1 e1
                 | uu____7799 ->
                     let uu____7800 =
                       let uu____7805 =
                         let uu____7806 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____7806
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____7805)  in
                     FStar_Errors.raise_err uu____7800
                  in
               let uu____7819 = flatten1 t_head  in
               (match uu____7819 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____7879 =
                          let uu____7884 =
                            let uu____7885 = FStar_Util.string_of_int n1  in
                            let uu____7892 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____7903 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____7885 uu____7892 uu____7903
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____7884)
                           in
                        FStar_Errors.raise_err uu____7879)
                     else ();
                     (let uu____7911 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____7911 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____7960 args1 =
                            match uu____7960 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____8040 =
                                       let uu____8041 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____8041.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____8040
                                 | (binders3,[]) ->
                                     let uu____8071 =
                                       let uu____8072 =
                                         let uu____8075 =
                                           let uu____8076 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____8076
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____8075
                                          in
                                       uu____8072.FStar_Syntax_Syntax.n  in
                                     (match uu____8071 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____8103 =
                                            let uu____8104 =
                                              let uu____8105 =
                                                let uu____8118 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____8118)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____8105
                                               in
                                            mk1 uu____8104  in
                                          N uu____8103
                                      | uu____8129 -> failwith "wat?")
                                 | ([],uu____8130::uu____8131) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____8171)::binders3,(arg,uu____8174)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____8237 = FStar_List.splitAt n' binders1  in
                          (match uu____8237 with
                           | (binders2,uu____8269) ->
                               let uu____8294 =
                                 let uu____8313 =
                                   FStar_List.map2
                                     (fun uu____8363  ->
                                        fun uu____8364  ->
                                          match (uu____8363, uu____8364) with
                                          | ((bv,uu____8400),(arg,q)) ->
                                              let uu____8417 =
                                                let uu____8418 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____8418.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____8417 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____8435 ->
                                                   let uu____8436 =
                                                     let uu____8441 =
                                                       star_type' env arg  in
                                                     (uu____8441, q)  in
                                                   (uu____8436, [(arg, q)])
                                               | uu____8468 ->
                                                   let uu____8469 =
                                                     check_n env arg  in
                                                   (match uu____8469 with
                                                    | (uu____8490,s_arg,u_arg)
                                                        ->
                                                        let uu____8493 =
                                                          let uu____8500 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____8500
                                                          then
                                                            let uu____8507 =
                                                              let uu____8512
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____8512, q)
                                                               in
                                                            [uu____8507;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____8493))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____8313  in
                               (match uu____8294 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____8601 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____8612 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____8601, uu____8612)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____8676) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____8682) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8688,uu____8689) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____8731 = let uu____8732 = env.tc_const c  in N uu____8732
             in
          (uu____8731, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____8739 ->
          let uu____8752 =
            let uu____8753 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____8753  in
          failwith uu____8752
      | FStar_Syntax_Syntax.Tm_type uu____8760 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____8767 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____8786 ->
          let uu____8793 =
            let uu____8794 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____8794  in
          failwith uu____8793
      | FStar_Syntax_Syntax.Tm_uvar uu____8801 ->
          let uu____8808 =
            let uu____8809 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____8809  in
          failwith uu____8808
      | FStar_Syntax_Syntax.Tm_delayed uu____8816 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____8847 =
            let uu____8848 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8848  in
          failwith uu____8847

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
          let uu____8895 = check_n env e0  in
          match uu____8895 with
          | (uu____8908,s_e0,u_e0) ->
              let uu____8911 =
                let uu____8940 =
                  FStar_List.map
                    (fun b  ->
                       let uu____9001 = FStar_Syntax_Subst.open_branch b  in
                       match uu____9001 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___121_9043 = env  in
                             let uu____9044 =
                               let uu____9045 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____9045
                                in
                             {
                               env = uu____9044;
                               subst = (uu___121_9043.subst);
                               tc_const = (uu___121_9043.tc_const)
                             }  in
                           let uu____9048 = f env1 body  in
                           (match uu____9048 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____9120 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____8940  in
              (match uu____8911 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____9224 = FStar_List.hd nms  in
                     match uu____9224 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___104_9232  ->
                          match uu___104_9232 with
                          | M uu____9233 -> true
                          | uu____9234 -> false) nms
                      in
                   let uu____9235 =
                     let uu____9272 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____9362  ->
                              match uu____9362 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____9539 =
                                         check env original_body (M t2)  in
                                       (match uu____9539 with
                                        | (uu____9576,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____9615,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____9272  in
                   (match uu____9235 with
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
                              (fun uu____9799  ->
                                 match uu____9799 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____9850 =
                                         let uu____9851 =
                                           let uu____9866 =
                                             let uu____9875 =
                                               let uu____9882 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____9885 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____9882, uu____9885)  in
                                             [uu____9875]  in
                                           (s_body, uu____9866)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____9851
                                          in
                                       mk1 uu____9850  in
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
                            let uu____10009 =
                              let uu____10010 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10010]  in
                            let uu____10023 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____10009 uu____10023
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____10047 =
                              let uu____10054 =
                                let uu____10059 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____10059
                                 in
                              [uu____10054]  in
                            let uu____10072 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____10047 uu____10072
                             in
                          let uu____10075 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____10114 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____10075, uu____10114)
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
                           let uu____10223 =
                             let uu____10224 =
                               let uu____10225 =
                                 let uu____10252 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____10252,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10225
                                in
                             mk1 uu____10224  in
                           let uu____10311 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____10223, uu____10311))))

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
              let uu____10374 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10374]  in
            let uu____10387 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____10387 with
            | (x_binders1,e21) ->
                let uu____10400 = infer env e1  in
                (match uu____10400 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____10417 = is_C t1  in
                       if uu____10417
                       then
                         let uu___122_10418 = binding  in
                         let uu____10419 =
                           let uu____10422 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____10422  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___122_10418.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___122_10418.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____10419;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___122_10418.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___122_10418.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___122_10418.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___122_10418.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___123_10425 = env  in
                       let uu____10426 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___124_10428 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_10428.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_10428.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10426;
                         subst = (uu___123_10425.subst);
                         tc_const = (uu___123_10425.tc_const)
                       }  in
                     let uu____10429 = proceed env1 e21  in
                     (match uu____10429 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___125_10446 = binding  in
                            let uu____10447 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___125_10446.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___125_10446.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____10447;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___125_10446.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___125_10446.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___125_10446.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___125_10446.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____10450 =
                            let uu____10451 =
                              let uu____10452 =
                                let uu____10465 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___126_10479 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_10479.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_10479.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_10479.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_10479.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___126_10479.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___126_10479.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10465)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10452  in
                            mk1 uu____10451  in
                          let uu____10480 =
                            let uu____10481 =
                              let uu____10482 =
                                let uu____10495 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___127_10509 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___127_10509.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___127_10509.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___127_10509.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___127_10509.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___127_10509.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___127_10509.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10495)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10482  in
                            mk1 uu____10481  in
                          (nm_rec, uu____10450, uu____10480))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___128_10514 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___128_10514.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___128_10514.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___128_10514.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___128_10514.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___128_10514.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___129_10516 = env  in
                       let uu____10517 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___130_10519 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___130_10519.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___130_10519.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10517;
                         subst = (uu___129_10516.subst);
                         tc_const = (uu___129_10516.tc_const)
                       }  in
                     let uu____10520 = ensure_m env1 e21  in
                     (match uu____10520 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____10543 =
                              let uu____10544 =
                                let uu____10559 =
                                  let uu____10568 =
                                    let uu____10575 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____10578 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____10575, uu____10578)  in
                                  [uu____10568]  in
                                (s_e2, uu____10559)  in
                              FStar_Syntax_Syntax.Tm_app uu____10544  in
                            mk1 uu____10543  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____10609 =
                              let uu____10610 =
                                let uu____10625 =
                                  let uu____10634 =
                                    let uu____10641 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____10641)  in
                                  [uu____10634]  in
                                (s_e1, uu____10625)  in
                              FStar_Syntax_Syntax.Tm_app uu____10610  in
                            mk1 uu____10609  in
                          let uu____10666 =
                            let uu____10667 =
                              let uu____10668 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10668]  in
                            FStar_Syntax_Util.abs uu____10667 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____10681 =
                            let uu____10682 =
                              let uu____10683 =
                                let uu____10696 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___131_10710 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___131_10710.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___131_10710.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___131_10710.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___131_10710.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___131_10710.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___131_10710.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10696)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10683  in
                            mk1 uu____10682  in
                          ((M t2), uu____10666, uu____10681)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10720 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____10720  in
      let uu____10721 = check env e mn  in
      match uu____10721 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10737 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10759 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____10759  in
      let uu____10760 = check env e mn  in
      match uu____10760 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10776 -> failwith "[check_m]: impossible"

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
        (let uu____10806 =
           let uu____10807 = is_C c  in Prims.op_Negation uu____10807  in
         if uu____10806 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____10817 =
           let uu____10818 = FStar_Syntax_Subst.compress c  in
           uu____10818.FStar_Syntax_Syntax.n  in
         match uu____10817 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____10843 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____10843 with
              | (wp_head,wp_args) ->
                  ((let uu____10881 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____10895 =
                           let uu____10896 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____10896
                            in
                         Prims.op_Negation uu____10895)
                       in
                    if uu____10881 then failwith "mismatch" else ());
                   (let uu____10904 =
                      let uu____10905 =
                        let uu____10920 =
                          FStar_List.map2
                            (fun uu____10950  ->
                               fun uu____10951  ->
                                 match (uu____10950, uu____10951) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____10990 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____10990
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____10993 =
                                           let uu____10998 =
                                             let uu____10999 =
                                               print_implicit q  in
                                             let uu____11000 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____10999 uu____11000
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____10998)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____10993)
                                      else ();
                                      (let uu____11002 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____11002, q)))) args wp_args
                           in
                        (head1, uu____10920)  in
                      FStar_Syntax_Syntax.Tm_app uu____10905  in
                    mk1 uu____10904)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____11038 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____11038 with
              | (binders_orig,comp1) ->
                  let uu____11045 =
                    let uu____11060 =
                      FStar_List.map
                        (fun uu____11094  ->
                           match uu____11094 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____11114 = is_C h  in
                               if uu____11114
                               then
                                 let w' =
                                   let uu____11126 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____11126
                                    in
                                 let uu____11127 =
                                   let uu____11134 =
                                     let uu____11141 =
                                       let uu____11146 =
                                         let uu____11147 =
                                           let uu____11148 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____11148  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____11147
                                          in
                                       (uu____11146, q)  in
                                     [uu____11141]  in
                                   (w', q) :: uu____11134  in
                                 (w', uu____11127)
                               else
                                 (let x =
                                    let uu____11169 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____11169
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____11060  in
                  (match uu____11045 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____11224 =
                           let uu____11227 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____11227
                            in
                         FStar_Syntax_Subst.subst_comp uu____11224 comp1  in
                       let app =
                         let uu____11231 =
                           let uu____11232 =
                             let uu____11247 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____11264 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____11265 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____11264, uu____11265)) bvs
                                in
                             (wp, uu____11247)  in
                           FStar_Syntax_Syntax.Tm_app uu____11232  in
                         mk1 uu____11231  in
                       let comp3 =
                         let uu____11277 = type_of_comp comp2  in
                         let uu____11278 = is_monadic_comp comp2  in
                         trans_G env uu____11277 uu____11278 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____11280,uu____11281) ->
             trans_F_ env e wp
         | uu____11322 -> failwith "impossible trans_F_")

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
            let uu____11327 =
              let uu____11328 = star_type' env h  in
              let uu____11331 =
                let uu____11340 =
                  let uu____11347 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____11347)  in
                [uu____11340]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____11328;
                FStar_Syntax_Syntax.effect_args = uu____11331;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____11327
          else
            (let uu____11363 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____11363)

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
    fun t  -> let uu____11382 = n env.env t  in star_type' env uu____11382
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____11401 = n env.env t  in check_n env uu____11401
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____11417 = n env.env c  in
        let uu____11418 = n env.env wp  in
        trans_F_ env uu____11417 uu____11418
  