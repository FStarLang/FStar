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
              let uu___79_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___79_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___79_123.FStar_Syntax_Syntax.index);
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
                      let uu____533 =
                        let uu____534 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____534  in
                      FStar_Syntax_Util.arrow gamma uu____533  in
                    let uu____535 =
                      let uu____536 =
                        let uu____543 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____548 =
                          let uu____555 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____555]  in
                        uu____543 :: uu____548  in
                      FStar_List.append binders uu____536  in
                    FStar_Syntax_Util.abs uu____535 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____576 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____577 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____576, uu____577)  in
                match uu____513 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____617 =
                        let uu____618 =
                          let uu____633 =
                            let uu____642 =
                              FStar_List.map
                                (fun uu____662  ->
                                   match uu____662 with
                                   | (bv,uu____672) ->
                                       let uu____673 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____674 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____673, uu____674)) binders
                               in
                            let uu____675 =
                              let uu____682 =
                                let uu____687 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____688 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____687, uu____688)  in
                              let uu____689 =
                                let uu____696 =
                                  let uu____701 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____701)  in
                                [uu____696]  in
                              uu____682 :: uu____689  in
                            FStar_List.append uu____642 uu____675  in
                          (fv, uu____633)  in
                        FStar_Syntax_Syntax.Tm_app uu____618  in
                      mk1 uu____617  in
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
                      let uu____770 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____770
                       in
                    let ret1 =
                      let uu____774 =
                        let uu____775 =
                          let uu____778 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____778  in
                        FStar_Syntax_Util.residual_tot uu____775  in
                      FStar_Pervasives_Native.Some uu____774  in
                    let body =
                      let uu____782 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____782 ret1  in
                    let uu____785 =
                      let uu____786 = mk_all_implicit binders  in
                      let uu____793 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____786 uu____793  in
                    FStar_Syntax_Util.abs uu____785 body ret1  in
                  let c_pure1 =
                    let uu____821 = mk_lid "pure"  in
                    register env1 uu____821 c_pure  in
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
                      let uu____828 =
                        let uu____829 =
                          let uu____830 =
                            let uu____837 =
                              let uu____842 =
                                let uu____843 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____843
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____842  in
                            [uu____837]  in
                          let uu____852 =
                            let uu____853 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____853  in
                          FStar_Syntax_Util.arrow uu____830 uu____852  in
                        mk_gctx uu____829  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____828
                       in
                    let r =
                      let uu____855 =
                        let uu____856 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____856  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____855
                       in
                    let ret1 =
                      let uu____860 =
                        let uu____861 =
                          let uu____864 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____864  in
                        FStar_Syntax_Util.residual_tot uu____861  in
                      FStar_Pervasives_Native.Some uu____860  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____874 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____877 =
                          let uu____886 =
                            let uu____889 =
                              let uu____890 =
                                let uu____891 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____891
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____890  in
                            [uu____889]  in
                          FStar_List.append gamma_as_args uu____886  in
                        FStar_Syntax_Util.mk_app uu____874 uu____877  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____894 =
                      let uu____895 = mk_all_implicit binders  in
                      let uu____902 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____895 uu____902  in
                    FStar_Syntax_Util.abs uu____894 outer_body ret1  in
                  let c_app1 =
                    let uu____938 = mk_lid "app"  in
                    register env1 uu____938 c_app  in
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
                      let uu____947 =
                        let uu____954 =
                          let uu____959 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____959  in
                        [uu____954]  in
                      let uu____968 =
                        let uu____969 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____969  in
                      FStar_Syntax_Util.arrow uu____947 uu____968  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____972 =
                        let uu____973 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____973  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____972
                       in
                    let ret1 =
                      let uu____977 =
                        let uu____978 =
                          let uu____981 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____981  in
                        FStar_Syntax_Util.residual_tot uu____978  in
                      FStar_Pervasives_Native.Some uu____977  in
                    let uu____982 =
                      let uu____983 = mk_all_implicit binders  in
                      let uu____990 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____983 uu____990  in
                    let uu____1025 =
                      let uu____1028 =
                        let uu____1037 =
                          let uu____1040 =
                            let uu____1041 =
                              let uu____1050 =
                                let uu____1053 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1053]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1050
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1041  in
                          let uu____1060 =
                            let uu____1063 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1063]  in
                          uu____1040 :: uu____1060  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1037
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1028  in
                    FStar_Syntax_Util.abs uu____982 uu____1025 ret1  in
                  let c_lift11 =
                    let uu____1071 = mk_lid "lift1"  in
                    register env1 uu____1071 c_lift1  in
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
                      let uu____1081 =
                        let uu____1088 =
                          let uu____1093 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1093  in
                        let uu____1094 =
                          let uu____1101 =
                            let uu____1106 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1106  in
                          [uu____1101]  in
                        uu____1088 :: uu____1094  in
                      let uu____1119 =
                        let uu____1120 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1120  in
                      FStar_Syntax_Util.arrow uu____1081 uu____1119  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1123 =
                        let uu____1124 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1124  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1123
                       in
                    let a2 =
                      let uu____1126 =
                        let uu____1127 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1127  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1126
                       in
                    let ret1 =
                      let uu____1131 =
                        let uu____1132 =
                          let uu____1135 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1135  in
                        FStar_Syntax_Util.residual_tot uu____1132  in
                      FStar_Pervasives_Native.Some uu____1131  in
                    let uu____1136 =
                      let uu____1137 = mk_all_implicit binders  in
                      let uu____1144 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1137 uu____1144  in
                    let uu____1187 =
                      let uu____1190 =
                        let uu____1199 =
                          let uu____1202 =
                            let uu____1203 =
                              let uu____1212 =
                                let uu____1215 =
                                  let uu____1216 =
                                    let uu____1225 =
                                      let uu____1228 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1228]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1225
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1216
                                   in
                                let uu____1235 =
                                  let uu____1238 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1238]  in
                                uu____1215 :: uu____1235  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1212
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1203  in
                          let uu____1245 =
                            let uu____1248 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1248]  in
                          uu____1202 :: uu____1245  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1199
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1190  in
                    FStar_Syntax_Util.abs uu____1136 uu____1187 ret1  in
                  let c_lift21 =
                    let uu____1256 = mk_lid "lift2"  in
                    register env1 uu____1256 c_lift2  in
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
                      let uu____1265 =
                        let uu____1272 =
                          let uu____1277 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1277  in
                        [uu____1272]  in
                      let uu____1286 =
                        let uu____1287 =
                          let uu____1288 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1288  in
                        FStar_Syntax_Syntax.mk_Total uu____1287  in
                      FStar_Syntax_Util.arrow uu____1265 uu____1286  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1293 =
                        let uu____1294 =
                          let uu____1297 =
                            let uu____1298 =
                              let uu____1305 =
                                let uu____1310 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1310
                                 in
                              [uu____1305]  in
                            let uu____1319 =
                              let uu____1320 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1320  in
                            FStar_Syntax_Util.arrow uu____1298 uu____1319  in
                          mk_ctx uu____1297  in
                        FStar_Syntax_Util.residual_tot uu____1294  in
                      FStar_Pervasives_Native.Some uu____1293  in
                    let e1 =
                      let uu____1322 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1322
                       in
                    let body =
                      let uu____1326 =
                        let uu____1327 =
                          let uu____1334 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1334]  in
                        FStar_List.append gamma uu____1327  in
                      let uu____1351 =
                        let uu____1354 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1357 =
                          let uu____1366 =
                            let uu____1367 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1367  in
                          let uu____1368 = args_of_binders1 gamma  in
                          uu____1366 :: uu____1368  in
                        FStar_Syntax_Util.mk_app uu____1354 uu____1357  in
                      FStar_Syntax_Util.abs uu____1326 uu____1351 ret1  in
                    let uu____1371 =
                      let uu____1372 = mk_all_implicit binders  in
                      let uu____1379 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1372 uu____1379  in
                    FStar_Syntax_Util.abs uu____1371 body ret1  in
                  let c_push1 =
                    let uu____1411 = mk_lid "push"  in
                    register env1 uu____1411 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1433 =
                        let uu____1434 =
                          let uu____1449 = args_of_binders1 binders  in
                          (c, uu____1449)  in
                        FStar_Syntax_Syntax.Tm_app uu____1434  in
                      mk1 uu____1433
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1473 =
                        let uu____1474 =
                          let uu____1481 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1486 =
                            let uu____1493 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1493]  in
                          uu____1481 :: uu____1486  in
                        let uu____1510 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1474 uu____1510  in
                      FStar_Syntax_Syntax.mk_Total uu____1473  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1512 =
                      let uu____1513 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1513  in
                    let uu____1524 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1528 =
                        let uu____1531 =
                          let uu____1540 =
                            let uu____1543 =
                              let uu____1544 =
                                let uu____1553 =
                                  let uu____1560 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1560  in
                                [uu____1553]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1544  in
                            [uu____1543]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1540
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1531  in
                      FStar_Syntax_Util.ascribe uu____1528
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1512 uu____1524
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1596 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1596 wp_if_then_else  in
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
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1609 =
                        let uu____1618 =
                          let uu____1621 =
                            let uu____1622 =
                              let uu____1631 =
                                let uu____1634 =
                                  let uu____1635 =
                                    let uu____1644 =
                                      let uu____1651 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1651
                                       in
                                    [uu____1644]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1635
                                   in
                                [uu____1634]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1631
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1622  in
                          let uu____1670 =
                            let uu____1673 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1673]  in
                          uu____1621 :: uu____1670  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1618
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1609  in
                    let uu____1680 =
                      let uu____1681 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1681  in
                    FStar_Syntax_Util.abs uu____1680 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1693 = mk_lid "wp_assert"  in
                    register env1 uu____1693 wp_assert  in
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
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1706 =
                        let uu____1715 =
                          let uu____1718 =
                            let uu____1719 =
                              let uu____1728 =
                                let uu____1731 =
                                  let uu____1732 =
                                    let uu____1741 =
                                      let uu____1748 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1748
                                       in
                                    [uu____1741]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1732
                                   in
                                [uu____1731]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1728
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1719  in
                          let uu____1767 =
                            let uu____1770 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1770]  in
                          uu____1718 :: uu____1767  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1715
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1706  in
                    let uu____1777 =
                      let uu____1778 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1778  in
                    FStar_Syntax_Util.abs uu____1777 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1790 = mk_lid "wp_assume"  in
                    register env1 uu____1790 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1801 =
                        let uu____1808 =
                          let uu____1813 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1813  in
                        [uu____1808]  in
                      let uu____1822 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1801 uu____1822  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1827 =
                        let uu____1836 =
                          let uu____1839 =
                            let uu____1840 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1840  in
                          let uu____1855 =
                            let uu____1858 =
                              let uu____1859 =
                                let uu____1868 =
                                  let uu____1871 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1871]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1868
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1859  in
                            [uu____1858]  in
                          uu____1839 :: uu____1855  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1836
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1827  in
                    let uu____1884 =
                      let uu____1885 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1885  in
                    FStar_Syntax_Util.abs uu____1884 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1897 = mk_lid "wp_close"  in
                    register env1 uu____1897 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1907 =
                      let uu____1908 =
                        let uu____1909 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1909
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1908  in
                    FStar_Pervasives_Native.Some uu____1907  in
                  let mk_forall1 x body =
                    let uu____1921 =
                      let uu____1928 =
                        let uu____1929 =
                          let uu____1944 =
                            let uu____1953 =
                              let uu____1960 =
                                let uu____1961 =
                                  let uu____1962 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1962]  in
                                FStar_Syntax_Util.abs uu____1961 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1960  in
                            [uu____1953]  in
                          (FStar_Syntax_Util.tforall, uu____1944)  in
                        FStar_Syntax_Syntax.Tm_app uu____1929  in
                      FStar_Syntax_Syntax.mk uu____1928  in
                    uu____1921 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2010 =
                      let uu____2011 = FStar_Syntax_Subst.compress t  in
                      uu____2011.FStar_Syntax_Syntax.n  in
                    match uu____2010 with
                    | FStar_Syntax_Syntax.Tm_type uu____2014 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2040  ->
                              match uu____2040 with
                              | (b,uu____2046) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2047 -> true  in
                  let rec is_monotonic t =
                    let uu____2054 =
                      let uu____2055 = FStar_Syntax_Subst.compress t  in
                      uu____2055.FStar_Syntax_Syntax.n  in
                    match uu____2054 with
                    | FStar_Syntax_Syntax.Tm_type uu____2058 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2084  ->
                              match uu____2084 with
                              | (b,uu____2090) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2091 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____2165 =
                      let uu____2166 = FStar_Syntax_Subst.compress t1  in
                      uu____2166.FStar_Syntax_Syntax.n  in
                    match uu____2165 with
                    | FStar_Syntax_Syntax.Tm_type uu____2171 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2174);
                                      FStar_Syntax_Syntax.pos = uu____2175;
                                      FStar_Syntax_Syntax.vars = uu____2176;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2210 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2210
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2217 =
                              let uu____2220 =
                                let uu____2229 =
                                  let uu____2236 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2236  in
                                [uu____2229]  in
                              FStar_Syntax_Util.mk_app x uu____2220  in
                            let uu____2249 =
                              let uu____2252 =
                                let uu____2261 =
                                  let uu____2268 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2268  in
                                [uu____2261]  in
                              FStar_Syntax_Util.mk_app y uu____2252  in
                            mk_rel1 b uu____2217 uu____2249  in
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
                             let uu____2285 =
                               let uu____2288 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2291 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2288 uu____2291  in
                             let uu____2294 =
                               let uu____2295 =
                                 let uu____2298 =
                                   let uu____2307 =
                                     let uu____2314 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2314
                                      in
                                   [uu____2307]  in
                                 FStar_Syntax_Util.mk_app x uu____2298  in
                               let uu____2327 =
                                 let uu____2330 =
                                   let uu____2339 =
                                     let uu____2346 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2346
                                      in
                                   [uu____2339]  in
                                 FStar_Syntax_Util.mk_app y uu____2330  in
                               mk_rel1 b uu____2295 uu____2327  in
                             FStar_Syntax_Util.mk_imp uu____2285 uu____2294
                              in
                           let uu____2359 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2359)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2362);
                                      FStar_Syntax_Syntax.pos = uu____2363;
                                      FStar_Syntax_Syntax.vars = uu____2364;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2398 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2398
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2405 =
                              let uu____2408 =
                                let uu____2417 =
                                  let uu____2424 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2424  in
                                [uu____2417]  in
                              FStar_Syntax_Util.mk_app x uu____2408  in
                            let uu____2437 =
                              let uu____2440 =
                                let uu____2449 =
                                  let uu____2456 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2456  in
                                [uu____2449]  in
                              FStar_Syntax_Util.mk_app y uu____2440  in
                            mk_rel1 b uu____2405 uu____2437  in
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
                             let uu____2473 =
                               let uu____2476 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2479 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2476 uu____2479  in
                             let uu____2482 =
                               let uu____2483 =
                                 let uu____2486 =
                                   let uu____2495 =
                                     let uu____2502 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2502
                                      in
                                   [uu____2495]  in
                                 FStar_Syntax_Util.mk_app x uu____2486  in
                               let uu____2515 =
                                 let uu____2518 =
                                   let uu____2527 =
                                     let uu____2534 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2534
                                      in
                                   [uu____2527]  in
                                 FStar_Syntax_Util.mk_app y uu____2518  in
                               mk_rel1 b uu____2483 uu____2515  in
                             FStar_Syntax_Util.mk_imp uu____2473 uu____2482
                              in
                           let uu____2547 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2547)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___80_2578 = t1  in
                          let uu____2579 =
                            let uu____2580 =
                              let uu____2593 =
                                let uu____2596 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2596  in
                              ([binder], uu____2593)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2580  in
                          {
                            FStar_Syntax_Syntax.n = uu____2579;
                            FStar_Syntax_Syntax.pos =
                              (uu___80_2578.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___80_2578.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2613 ->
                        failwith "unhandled arrow"
                    | uu____2628 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                            FStar_Syntax_Syntax.Delta_constant] env1 t
                         in
                      let uu____2665 =
                        let uu____2666 = FStar_Syntax_Subst.compress t1  in
                        uu____2666.FStar_Syntax_Syntax.n  in
                      match uu____2665 with
                      | FStar_Syntax_Syntax.Tm_type uu____2671 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2694 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2694
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2713 =
                                let uu____2714 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2714 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2713
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2737 =
                            let uu____2746 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2766  ->
                                     match uu____2766 with
                                     | (t2,q) ->
                                         let uu____2781 = project i x  in
                                         let uu____2784 = project i y  in
                                         mk_stronger t2 uu____2781 uu____2784)
                                args
                               in
                            match uu____2746 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2737 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2837);
                                      FStar_Syntax_Syntax.pos = uu____2838;
                                      FStar_Syntax_Syntax.vars = uu____2839;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2877  ->
                                   match uu____2877 with
                                   | (bv,q) ->
                                       let uu____2884 =
                                         let uu____2885 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2885  in
                                       FStar_Syntax_Syntax.gen_bv uu____2884
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2892 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2892) bvs
                             in
                          let body =
                            let uu____2896 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2899 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2896 uu____2899  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2908);
                                      FStar_Syntax_Syntax.pos = uu____2909;
                                      FStar_Syntax_Syntax.vars = uu____2910;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2948  ->
                                   match uu____2948 with
                                   | (bv,q) ->
                                       let uu____2955 =
                                         let uu____2956 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2956  in
                                       FStar_Syntax_Syntax.gen_bv uu____2955
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2963 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2963) bvs
                             in
                          let body =
                            let uu____2967 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2970 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2967 uu____2970  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2977 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2983 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2986 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____2989 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2983 uu____2986 uu____2989  in
                    let uu____2992 =
                      let uu____2993 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____2993  in
                    FStar_Syntax_Util.abs uu____2992 body ret_tot_type  in
                  let stronger1 =
                    let uu____3021 = mk_lid "stronger"  in
                    register env1 uu____3021 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3029 = FStar_Util.prefix gamma  in
                    match uu____3029 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3078 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3078
                             in
                          let uu____3081 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3081 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3089 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3089  in
                              let guard_free1 =
                                let uu____3099 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3099  in
                              let pat =
                                let uu____3103 =
                                  let uu____3112 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3112]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3103
                                 in
                              let pattern_guarded_body =
                                let uu____3134 =
                                  let uu____3135 =
                                    let uu____3142 =
                                      let uu____3143 =
                                        let uu____3154 =
                                          let uu____3163 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3163]  in
                                        [uu____3154]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3143
                                       in
                                    (body, uu____3142)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3135  in
                                mk1 uu____3134  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3182 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3188 =
                            let uu____3191 =
                              let uu____3192 =
                                let uu____3193 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3196 =
                                  let uu____3205 = args_of_binders1 wp_args
                                     in
                                  let uu____3208 =
                                    let uu____3211 =
                                      let uu____3212 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3212
                                       in
                                    [uu____3211]  in
                                  FStar_List.append uu____3205 uu____3208  in
                                FStar_Syntax_Util.mk_app uu____3193
                                  uu____3196
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3192  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3191
                             in
                          FStar_Syntax_Util.abs gamma uu____3188
                            ret_gtot_type
                           in
                        let uu____3213 =
                          let uu____3214 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3214  in
                        FStar_Syntax_Util.abs uu____3213 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3226 = mk_lid "wp_ite"  in
                    register env1 uu____3226 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3234 = FStar_Util.prefix gamma  in
                    match uu____3234 with
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
                      let uu___81_3484 = ed  in
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
                          (uu___81_3484.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___81_3484.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___81_3484.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___81_3484.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___81_3484.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___81_3484.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___81_3484.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3485;
                        FStar_Syntax_Syntax.ite_wp = uu____3493;
                        FStar_Syntax_Syntax.stronger = uu____3501;
                        FStar_Syntax_Syntax.close_wp = uu____3509;
                        FStar_Syntax_Syntax.assert_p = uu____3517;
                        FStar_Syntax_Syntax.assume_p = uu____3525;
                        FStar_Syntax_Syntax.null_wp = uu____3533;
                        FStar_Syntax_Syntax.trivial = uu____3541;
                        FStar_Syntax_Syntax.repr =
                          (uu___81_3484.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___81_3484.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___81_3484.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___81_3484.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___81_3484.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____3430, uu____3483)))))
  
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___82_3564 = dmff_env  in
      {
        env = env';
        subst = (uu___82_3564.subst);
        tc_const = (uu___82_3564.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____3581 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____3595 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___68_3607  ->
    match uu___68_3607 with
    | FStar_Syntax_Syntax.Total (t,uu____3609) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___67_3622  ->
                match uu___67_3622 with
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
  fun uu___69_3641  ->
    match uu___69_3641 with
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
    let uu____3729 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3729
  
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
        let uu____3770 =
          let uu____3771 =
            let uu____3784 =
              let uu____3791 =
                let uu____3796 =
                  let uu____3797 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____3797  in
                let uu____3798 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____3796, uu____3798)  in
              [uu____3791]  in
            let uu____3807 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____3784, uu____3807)  in
          FStar_Syntax_Syntax.Tm_arrow uu____3771  in
        mk1 uu____3770

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3845) ->
          let binders1 =
            FStar_List.map
              (fun uu____3881  ->
                 match uu____3881 with
                 | (bv,aqual) ->
                     let uu____3892 =
                       let uu___83_3893 = bv  in
                       let uu____3894 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___83_3893.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___83_3893.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3894
                       }  in
                     (uu____3892, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3897,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3899);
                             FStar_Syntax_Syntax.pos = uu____3900;
                             FStar_Syntax_Syntax.vars = uu____3901;_})
               ->
               let uu____3926 =
                 let uu____3927 =
                   let uu____3940 =
                     let uu____3943 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3943  in
                   (binders1, uu____3940)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3927  in
               mk1 uu____3926
           | uu____3952 ->
               let uu____3953 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3953 with
                | N hn ->
                    let uu____3955 =
                      let uu____3956 =
                        let uu____3969 =
                          let uu____3972 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3972  in
                        (binders1, uu____3969)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3956  in
                    mk1 uu____3955
                | M a ->
                    let uu____3982 =
                      let uu____3983 =
                        let uu____3996 =
                          let uu____4003 =
                            let uu____4010 =
                              let uu____4015 =
                                let uu____4016 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4016  in
                              let uu____4017 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4015, uu____4017)  in
                            [uu____4010]  in
                          FStar_List.append binders1 uu____4003  in
                        let uu____4030 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3996, uu____4030)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3983  in
                    mk1 uu____3982))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4112 = f x  in
                    FStar_Util.string_builder_append strb uu____4112);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4119 = f x1  in
                         FStar_Util.string_builder_append strb uu____4119))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4121 =
              let uu____4126 =
                let uu____4127 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4128 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4127 uu____4128
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4126)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4121  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4144 =
              let uu____4145 = FStar_Syntax_Subst.compress ty  in
              uu____4145.FStar_Syntax_Syntax.n  in
            match uu____4144 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4166 =
                  let uu____4167 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4167  in
                if uu____4166
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____4197 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____4197 s  in
                       let uu____4200 =
                         let uu____4201 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____4201  in
                       if uu____4200
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____4204 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____4204 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____4226  ->
                                  match uu____4226 with
                                  | (bv,uu____4236) ->
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
            | uu____4250 ->
                ((let uu____4252 =
                    let uu____4257 =
                      let uu____4258 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4258
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4257)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4252);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4265 =
              let uu____4266 = FStar_Syntax_Subst.compress head2  in
              uu____4266.FStar_Syntax_Syntax.n  in
            match uu____4265 with
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
                  (let uu____4271 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4271)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4273 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4273 with
                 | ((uu____4282,ty),uu____4284) ->
                     let uu____4289 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4289
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       let uu____4297 =
                         let uu____4298 = FStar_Syntax_Subst.compress res  in
                         uu____4298.FStar_Syntax_Syntax.n  in
                       (match uu____4297 with
                        | FStar_Syntax_Syntax.Tm_app uu____4301 -> true
                        | uu____4316 ->
                            ((let uu____4318 =
                                let uu____4323 =
                                  let uu____4324 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____4324
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____4323)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____4318);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____4326 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4327 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4329) ->
                is_valid_application t2
            | uu____4334 -> false  in
          let uu____4335 = is_valid_application head1  in
          if uu____4335
          then
            let uu____4336 =
              let uu____4337 =
                let uu____4352 =
                  FStar_List.map
                    (fun uu____4375  ->
                       match uu____4375 with
                       | (t2,qual) ->
                           let uu____4392 = star_type' env t2  in
                           (uu____4392, qual)) args
                   in
                (head1, uu____4352)  in
              FStar_Syntax_Syntax.Tm_app uu____4337  in
            mk1 uu____4336
          else
            (let uu____4404 =
               let uu____4409 =
                 let uu____4410 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____4410
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____4409)  in
             FStar_Errors.raise_err uu____4404)
      | FStar_Syntax_Syntax.Tm_bvar uu____4411 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____4412 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____4413 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____4414 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____4438 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____4438 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___86_4446 = env  in
                 let uu____4447 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____4447;
                   subst = (uu___86_4446.subst);
                   tc_const = (uu___86_4446.tc_const)
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
               ((let uu___87_4469 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___87_4469.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___87_4469.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____4476 =
            let uu____4477 =
              let uu____4484 = star_type' env t2  in (uu____4484, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____4477  in
          mk1 uu____4476
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____4536 =
            let uu____4537 =
              let uu____4564 = star_type' env e  in
              let uu____4567 =
                let uu____4584 =
                  let uu____4591 = star_type' env t2  in
                  FStar_Util.Inl uu____4591  in
                (uu____4584, FStar_Pervasives_Native.None)  in
              (uu____4564, uu____4567, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4537  in
          mk1 uu____4536
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____4673 =
            let uu____4674 =
              let uu____4701 = star_type' env e  in
              let uu____4704 =
                let uu____4721 =
                  let uu____4728 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4728  in
                (uu____4721, FStar_Pervasives_Native.None)  in
              (uu____4701, uu____4704, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4674  in
          mk1 uu____4673
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4763,(uu____4764,FStar_Pervasives_Native.Some uu____4765),uu____4766)
          ->
          let uu____4815 =
            let uu____4820 =
              let uu____4821 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4821
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4820)  in
          FStar_Errors.raise_err uu____4815
      | FStar_Syntax_Syntax.Tm_refine uu____4822 ->
          let uu____4829 =
            let uu____4834 =
              let uu____4835 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4835
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4834)  in
          FStar_Errors.raise_err uu____4829
      | FStar_Syntax_Syntax.Tm_uinst uu____4836 ->
          let uu____4843 =
            let uu____4848 =
              let uu____4849 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4849
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4848)  in
          FStar_Errors.raise_err uu____4843
      | FStar_Syntax_Syntax.Tm_quoted uu____4850 ->
          let uu____4857 =
            let uu____4862 =
              let uu____4863 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4863
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4862)  in
          FStar_Errors.raise_err uu____4857
      | FStar_Syntax_Syntax.Tm_constant uu____4864 ->
          let uu____4865 =
            let uu____4870 =
              let uu____4871 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4871
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4870)  in
          FStar_Errors.raise_err uu____4865
      | FStar_Syntax_Syntax.Tm_match uu____4872 ->
          let uu____4895 =
            let uu____4900 =
              let uu____4901 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4901
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4900)  in
          FStar_Errors.raise_err uu____4895
      | FStar_Syntax_Syntax.Tm_let uu____4902 ->
          let uu____4915 =
            let uu____4920 =
              let uu____4921 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4921
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4920)  in
          FStar_Errors.raise_err uu____4915
      | FStar_Syntax_Syntax.Tm_uvar uu____4922 ->
          let uu____4923 =
            let uu____4928 =
              let uu____4929 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4929
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4928)  in
          FStar_Errors.raise_err uu____4923
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4930 =
            let uu____4935 =
              let uu____4936 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4936
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4935)  in
          FStar_Errors.raise_err uu____4930
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4938 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4938
      | FStar_Syntax_Syntax.Tm_delayed uu____4941 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___71_4972  ->
    match uu___71_4972 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___70_4979  ->
                match uu___70_4979 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4980 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____4986 =
      let uu____4987 = FStar_Syntax_Subst.compress t  in
      uu____4987.FStar_Syntax_Syntax.n  in
    match uu____4986 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5013 =
            let uu____5014 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5014  in
          is_C uu____5013  in
        if r
        then
          ((let uu____5030 =
              let uu____5031 =
                FStar_List.for_all
                  (fun uu____5039  ->
                     match uu____5039 with | (h,uu____5045) -> is_C h) args
                 in
              Prims.op_Negation uu____5031  in
            if uu____5030 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5049 =
              let uu____5050 =
                FStar_List.for_all
                  (fun uu____5059  ->
                     match uu____5059 with
                     | (h,uu____5065) ->
                         let uu____5066 = is_C h  in
                         Prims.op_Negation uu____5066) args
                 in
              Prims.op_Negation uu____5050  in
            if uu____5049 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5086 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5086 with
         | M t1 ->
             ((let uu____5089 = is_C t1  in
               if uu____5089 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5093) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5099) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5105,uu____5106) -> is_C t1
    | uu____5147 -> false
  
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
          let uu____5180 =
            let uu____5181 =
              let uu____5196 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____5199 =
                let uu____5208 =
                  let uu____5213 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____5213)  in
                [uu____5208]  in
              (uu____5196, uu____5199)  in
            FStar_Syntax_Syntax.Tm_app uu____5181  in
          mk1 uu____5180  in
        let uu____5232 =
          let uu____5233 = FStar_Syntax_Syntax.mk_binder p  in [uu____5233]
           in
        FStar_Syntax_Util.abs uu____5232 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___72_5250  ->
    match uu___72_5250 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5251 -> false
  
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
        let return_if uu____5484 =
          match uu____5484 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____5511 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____5513 =
                       let uu____5514 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____5514  in
                     Prims.op_Negation uu____5513)
                   in
                if uu____5511
                then
                  let uu____5515 =
                    let uu____5520 =
                      let uu____5521 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____5522 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____5523 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____5521 uu____5522 uu____5523
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____5520)  in
                  FStar_Errors.raise_err uu____5515
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____5540 = mk_return env t1 s_e  in
                     ((M t1), uu____5540, u_e)))
               | (M t1,N t2) ->
                   let uu____5547 =
                     let uu____5552 =
                       let uu____5553 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____5554 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____5555 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____5553 uu____5554 uu____5555
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____5552)
                      in
                   FStar_Errors.raise_err uu____5547)
           in
        let ensure_m env1 e2 =
          let strip_m uu___73_5602 =
            match uu___73_5602 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____5618 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____5638 =
                let uu____5643 =
                  let uu____5644 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____5644
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____5643)  in
              FStar_Errors.raise_error uu____5638 e2.FStar_Syntax_Syntax.pos
          | M uu____5651 ->
              let uu____5652 = check env1 e2 context_nm  in
              strip_m uu____5652
           in
        let uu____5659 =
          let uu____5660 = FStar_Syntax_Subst.compress e  in
          uu____5660.FStar_Syntax_Syntax.n  in
        match uu____5659 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5669 ->
            let uu____5670 = infer env e  in return_if uu____5670
        | FStar_Syntax_Syntax.Tm_name uu____5677 ->
            let uu____5678 = infer env e  in return_if uu____5678
        | FStar_Syntax_Syntax.Tm_fvar uu____5685 ->
            let uu____5686 = infer env e  in return_if uu____5686
        | FStar_Syntax_Syntax.Tm_abs uu____5693 ->
            let uu____5710 = infer env e  in return_if uu____5710
        | FStar_Syntax_Syntax.Tm_constant uu____5717 ->
            let uu____5718 = infer env e  in return_if uu____5718
        | FStar_Syntax_Syntax.Tm_quoted uu____5725 ->
            let uu____5732 = infer env e  in return_if uu____5732
        | FStar_Syntax_Syntax.Tm_app uu____5739 ->
            let uu____5754 = infer env e  in return_if uu____5754
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5762 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5762 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5824) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5830) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5836,uu____5837) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5878 ->
            let uu____5891 =
              let uu____5892 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5892  in
            failwith uu____5891
        | FStar_Syntax_Syntax.Tm_type uu____5899 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5906 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5925 ->
            let uu____5932 =
              let uu____5933 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5933  in
            failwith uu____5932
        | FStar_Syntax_Syntax.Tm_uvar uu____5940 ->
            let uu____5941 =
              let uu____5942 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5942  in
            failwith uu____5941
        | FStar_Syntax_Syntax.Tm_delayed uu____5949 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5980 =
              let uu____5981 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5981  in
            failwith uu____5980

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
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env
         in
      let uu____6009 =
        let uu____6010 = FStar_Syntax_Subst.compress e  in
        uu____6010.FStar_Syntax_Syntax.n  in
      match uu____6009 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6028 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6028
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6075;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____6076;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6082 =
                  let uu___88_6083 = rc  in
                  let uu____6084 =
                    let uu____6089 =
                      let uu____6092 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____6092  in
                    FStar_Pervasives_Native.Some uu____6089  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___88_6083.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6084;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___88_6083.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____6082
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___89_6104 = env  in
            let uu____6105 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____6105;
              subst = (uu___89_6104.subst);
              tc_const = (uu___89_6104.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____6125  ->
                 match uu____6125 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___90_6138 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___90_6138.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___90_6138.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____6139 =
            FStar_List.fold_left
              (fun uu____6168  ->
                 fun uu____6169  ->
                   match (uu____6168, uu____6169) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____6217 = is_C c  in
                       if uu____6217
                       then
                         let xw =
                           let uu____6225 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____6225
                            in
                         let x =
                           let uu___91_6227 = bv  in
                           let uu____6228 =
                             let uu____6231 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____6231  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___91_6227.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___91_6227.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____6228
                           }  in
                         let env3 =
                           let uu___92_6233 = env2  in
                           let uu____6234 =
                             let uu____6237 =
                               let uu____6238 =
                                 let uu____6245 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____6245)  in
                               FStar_Syntax_Syntax.NT uu____6238  in
                             uu____6237 :: (env2.subst)  in
                           {
                             env = (uu___92_6233.env);
                             subst = uu____6234;
                             tc_const = (uu___92_6233.tc_const)
                           }  in
                         let uu____6250 =
                           let uu____6253 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____6254 =
                             let uu____6257 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____6257 :: acc  in
                           uu____6253 :: uu____6254  in
                         (env3, uu____6250)
                       else
                         (let x =
                            let uu___93_6262 = bv  in
                            let uu____6263 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_6262.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_6262.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____6263
                            }  in
                          let uu____6266 =
                            let uu____6269 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____6269 :: acc  in
                          (env2, uu____6266))) (env1, []) binders1
             in
          (match uu____6139 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____6289 =
                 let check_what =
                   let uu____6315 = is_monadic rc_opt1  in
                   if uu____6315 then check_m else check_n  in
                 let uu____6331 = check_what env2 body1  in
                 match uu____6331 with
                 | (t,s_body,u_body) ->
                     let uu____6355 =
                       let uu____6356 =
                         let uu____6357 = is_monadic rc_opt1  in
                         if uu____6357 then M t else N t  in
                       comp_of_nm uu____6356  in
                     (uu____6355, s_body, u_body)
                  in
               (match uu____6289 with
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
                                 let uu____6388 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___74_6392  ->
                                           match uu___74_6392 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____6393 -> false))
                                    in
                                 if uu____6388
                                 then
                                   let uu____6394 =
                                     FStar_List.filter
                                       (fun uu___75_6398  ->
                                          match uu___75_6398 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____6399 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____6394
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____6408 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___76_6412  ->
                                         match uu___76_6412 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____6413 -> false))
                                  in
                               if uu____6408
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___77_6420  ->
                                        match uu___77_6420 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____6421 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____6422 =
                                   let uu____6423 =
                                     let uu____6428 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____6428
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____6423 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____6422
                               else
                                 (let uu____6434 =
                                    let uu___94_6435 = rc  in
                                    let uu____6436 =
                                      let uu____6441 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____6441
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___94_6435.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____6436;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___94_6435.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____6434))
                       in
                    let uu____6446 =
                      let comp1 =
                        let uu____6456 = is_monadic rc_opt1  in
                        let uu____6457 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____6456 uu____6457
                         in
                      let uu____6458 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____6458,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____6446 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____6502 =
                             let uu____6503 =
                               let uu____6520 =
                                 let uu____6523 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____6523 s_rc_opt  in
                               (s_binders1, s_body1, uu____6520)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6503  in
                           mk1 uu____6502  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____6541 =
                             let uu____6542 =
                               let uu____6559 =
                                 let uu____6562 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____6562 u_rc_opt  in
                               (u_binders2, u_body2, uu____6559)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6542  in
                           mk1 uu____6541  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____6576;_};
            FStar_Syntax_Syntax.fv_delta = uu____6577;
            FStar_Syntax_Syntax.fv_qual = uu____6578;_}
          ->
          let uu____6581 =
            let uu____6586 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6586  in
          (match uu____6581 with
           | (uu____6617,t) ->
               let uu____6619 =
                 let uu____6620 = normalize1 t  in N uu____6620  in
               (uu____6619, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6621;
             FStar_Syntax_Syntax.vars = uu____6622;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6685 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6685 with
           | (unary_op,uu____6707) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6766;
             FStar_Syntax_Syntax.vars = uu____6767;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6843 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6843 with
           | (unary_op,uu____6865) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6930;
             FStar_Syntax_Syntax.vars = uu____6931;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____6961 = infer env a  in
          (match uu____6961 with
           | (t,s,u) ->
               let uu____6977 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6977 with
                | (head1,uu____6999) ->
                    let uu____7020 =
                      let uu____7021 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____7021  in
                    let uu____7022 =
                      let uu____7023 =
                        let uu____7024 =
                          let uu____7039 =
                            let uu____7048 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7048]  in
                          (head1, uu____7039)  in
                        FStar_Syntax_Syntax.Tm_app uu____7024  in
                      mk1 uu____7023  in
                    let uu____7059 =
                      let uu____7060 =
                        let uu____7061 =
                          let uu____7076 =
                            let uu____7085 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7085]  in
                          (head1, uu____7076)  in
                        FStar_Syntax_Syntax.Tm_app uu____7061  in
                      mk1 uu____7060  in
                    (uu____7020, uu____7022, uu____7059)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7096;
             FStar_Syntax_Syntax.vars = uu____7097;_},(a1,uu____7099)::a2::[])
          ->
          let uu____7141 = infer env a1  in
          (match uu____7141 with
           | (t,s,u) ->
               let uu____7157 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7157 with
                | (head1,uu____7179) ->
                    let uu____7200 =
                      let uu____7201 =
                        let uu____7202 =
                          let uu____7217 =
                            let uu____7226 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7226; a2]  in
                          (head1, uu____7217)  in
                        FStar_Syntax_Syntax.Tm_app uu____7202  in
                      mk1 uu____7201  in
                    let uu____7237 =
                      let uu____7238 =
                        let uu____7239 =
                          let uu____7254 =
                            let uu____7263 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7263; a2]  in
                          (head1, uu____7254)  in
                        FStar_Syntax_Syntax.Tm_app uu____7239  in
                      mk1 uu____7238  in
                    (t, uu____7200, uu____7237)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7274;
             FStar_Syntax_Syntax.vars = uu____7275;_},uu____7276)
          ->
          let uu____7297 =
            let uu____7302 =
              let uu____7303 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7303
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7302)  in
          FStar_Errors.raise_error uu____7297 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7310;
             FStar_Syntax_Syntax.vars = uu____7311;_},uu____7312)
          ->
          let uu____7333 =
            let uu____7338 =
              let uu____7339 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7339
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7338)  in
          FStar_Errors.raise_error uu____7333 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____7368 = check_n env head1  in
          (match uu____7368 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____7390 =
                   let uu____7391 = FStar_Syntax_Subst.compress t  in
                   uu____7391.FStar_Syntax_Syntax.n  in
                 match uu____7390 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____7394 -> true
                 | uu____7407 -> false  in
               let rec flatten1 t =
                 let uu____7426 =
                   let uu____7427 = FStar_Syntax_Subst.compress t  in
                   uu____7427.FStar_Syntax_Syntax.n  in
                 match uu____7426 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____7444);
                                FStar_Syntax_Syntax.pos = uu____7445;
                                FStar_Syntax_Syntax.vars = uu____7446;_})
                     when is_arrow t1 ->
                     let uu____7471 = flatten1 t1  in
                     (match uu____7471 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7553,uu____7554)
                     -> flatten1 e1
                 | uu____7595 ->
                     let uu____7596 =
                       let uu____7601 =
                         let uu____7602 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____7602
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____7601)  in
                     FStar_Errors.raise_err uu____7596
                  in
               let uu____7615 = flatten1 t_head  in
               (match uu____7615 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____7675 =
                          let uu____7680 =
                            let uu____7681 = FStar_Util.string_of_int n1  in
                            let uu____7688 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____7699 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____7681 uu____7688 uu____7699
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____7680)
                           in
                        FStar_Errors.raise_err uu____7675)
                     else ();
                     (let uu____7707 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____7707 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____7756 args1 =
                            match uu____7756 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____7836 =
                                       let uu____7837 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____7837.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____7836
                                 | (binders3,[]) ->
                                     let uu____7867 =
                                       let uu____7868 =
                                         let uu____7871 =
                                           let uu____7872 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____7872
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____7871
                                          in
                                       uu____7868.FStar_Syntax_Syntax.n  in
                                     (match uu____7867 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____7899 =
                                            let uu____7900 =
                                              let uu____7901 =
                                                let uu____7914 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____7914)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____7901
                                               in
                                            mk1 uu____7900  in
                                          N uu____7899
                                      | uu____7925 -> failwith "wat?")
                                 | ([],uu____7926::uu____7927) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____7967)::binders3,(arg,uu____7970)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____8033 = FStar_List.splitAt n' binders1  in
                          (match uu____8033 with
                           | (binders2,uu____8065) ->
                               let uu____8090 =
                                 let uu____8109 =
                                   FStar_List.map2
                                     (fun uu____8157  ->
                                        fun uu____8158  ->
                                          match (uu____8157, uu____8158) with
                                          | ((bv,uu____8190),(arg,q)) ->
                                              let uu____8201 =
                                                let uu____8202 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____8202.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____8201 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____8219 ->
                                                   let uu____8220 =
                                                     let uu____8225 =
                                                       star_type' env arg  in
                                                     (uu____8225, q)  in
                                                   (uu____8220, [(arg, q)])
                                               | uu____8244 ->
                                                   let uu____8245 =
                                                     check_n env arg  in
                                                   (match uu____8245 with
                                                    | (uu____8266,s_arg,u_arg)
                                                        ->
                                                        let uu____8269 =
                                                          let uu____8276 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____8276
                                                          then
                                                            let uu____8283 =
                                                              let uu____8288
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____8288, q)
                                                               in
                                                            [uu____8283;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____8269))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____8109  in
                               (match uu____8090 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____8377 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____8388 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____8377, uu____8388)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____8452) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____8458) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8464,uu____8465) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____8507 = let uu____8508 = env.tc_const c  in N uu____8508
             in
          (uu____8507, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____8515 ->
          let uu____8528 =
            let uu____8529 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____8529  in
          failwith uu____8528
      | FStar_Syntax_Syntax.Tm_type uu____8536 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____8543 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____8562 ->
          let uu____8569 =
            let uu____8570 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____8570  in
          failwith uu____8569
      | FStar_Syntax_Syntax.Tm_uvar uu____8577 ->
          let uu____8578 =
            let uu____8579 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____8579  in
          failwith uu____8578
      | FStar_Syntax_Syntax.Tm_delayed uu____8586 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____8617 =
            let uu____8618 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8618  in
          failwith uu____8617

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
          let uu____8665 = check_n env e0  in
          match uu____8665 with
          | (uu____8678,s_e0,u_e0) ->
              let uu____8681 =
                let uu____8710 =
                  FStar_List.map
                    (fun b  ->
                       let uu____8771 = FStar_Syntax_Subst.open_branch b  in
                       match uu____8771 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___95_8813 = env  in
                             let uu____8814 =
                               let uu____8815 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____8815
                                in
                             {
                               env = uu____8814;
                               subst = (uu___95_8813.subst);
                               tc_const = (uu___95_8813.tc_const)
                             }  in
                           let uu____8818 = f env1 body  in
                           (match uu____8818 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8890 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____8710  in
              (match uu____8681 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8994 = FStar_List.hd nms  in
                     match uu____8994 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___78_9002  ->
                          match uu___78_9002 with
                          | M uu____9003 -> true
                          | uu____9004 -> false) nms
                      in
                   let uu____9005 =
                     let uu____9042 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____9132  ->
                              match uu____9132 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____9309 =
                                         check env original_body (M t2)  in
                                       (match uu____9309 with
                                        | (uu____9346,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____9385,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____9042  in
                   (match uu____9005 with
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
                              (fun uu____9569  ->
                                 match uu____9569 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____9620 =
                                         let uu____9621 =
                                           let uu____9636 =
                                             let uu____9645 =
                                               let uu____9650 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____9651 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____9650, uu____9651)  in
                                             [uu____9645]  in
                                           (s_body, uu____9636)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____9621
                                          in
                                       mk1 uu____9620  in
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
                            let uu____9713 =
                              let uu____9714 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9714]  in
                            let uu____9727 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____9713 uu____9727
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____9751 =
                              let uu____9758 =
                                let uu____9763 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____9763
                                 in
                              [uu____9758]  in
                            let uu____9776 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____9751 uu____9776  in
                          let uu____9777 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____9816 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____9777, uu____9816)
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
                           let uu____9869 =
                             let uu____9870 =
                               let uu____9871 =
                                 let uu____9898 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____9898,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____9871  in
                             mk1 uu____9870  in
                           let uu____9957 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____9869, uu____9957))))

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
              let uu____10020 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10020]  in
            let uu____10033 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____10033 with
            | (x_binders1,e21) ->
                let uu____10046 = infer env e1  in
                (match uu____10046 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____10063 = is_C t1  in
                       if uu____10063
                       then
                         let uu___96_10064 = binding  in
                         let uu____10065 =
                           let uu____10068 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____10068  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___96_10064.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___96_10064.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____10065;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___96_10064.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___96_10064.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___96_10064.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___96_10064.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___97_10071 = env  in
                       let uu____10072 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___98_10074 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___98_10074.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___98_10074.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10072;
                         subst = (uu___97_10071.subst);
                         tc_const = (uu___97_10071.tc_const)
                       }  in
                     let uu____10075 = proceed env1 e21  in
                     (match uu____10075 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___99_10092 = binding  in
                            let uu____10093 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___99_10092.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___99_10092.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____10093;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___99_10092.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___99_10092.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___99_10092.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___99_10092.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____10096 =
                            let uu____10097 =
                              let uu____10098 =
                                let uu____10111 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___100_10125 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___100_10125.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___100_10125.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___100_10125.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___100_10125.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___100_10125.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___100_10125.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10111)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10098  in
                            mk1 uu____10097  in
                          let uu____10126 =
                            let uu____10127 =
                              let uu____10128 =
                                let uu____10141 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___101_10155 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___101_10155.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___101_10155.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___101_10155.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___101_10155.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___101_10155.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___101_10155.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10141)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10128  in
                            mk1 uu____10127  in
                          (nm_rec, uu____10096, uu____10126))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___102_10160 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___102_10160.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___102_10160.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___102_10160.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___102_10160.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___102_10160.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___103_10162 = env  in
                       let uu____10163 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___104_10165 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___104_10165.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___104_10165.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10163;
                         subst = (uu___103_10162.subst);
                         tc_const = (uu___103_10162.tc_const)
                       }  in
                     let uu____10166 = ensure_m env1 e21  in
                     (match uu____10166 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____10189 =
                              let uu____10190 =
                                let uu____10205 =
                                  let uu____10214 =
                                    let uu____10219 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____10220 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____10219, uu____10220)  in
                                  [uu____10214]  in
                                (s_e2, uu____10205)  in
                              FStar_Syntax_Syntax.Tm_app uu____10190  in
                            mk1 uu____10189  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____10245 =
                              let uu____10246 =
                                let uu____10261 =
                                  let uu____10270 =
                                    let uu____10277 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____10277)  in
                                  [uu____10270]  in
                                (s_e1, uu____10261)  in
                              FStar_Syntax_Syntax.Tm_app uu____10246  in
                            mk1 uu____10245  in
                          let uu____10302 =
                            let uu____10303 =
                              let uu____10304 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10304]  in
                            FStar_Syntax_Util.abs uu____10303 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____10317 =
                            let uu____10318 =
                              let uu____10319 =
                                let uu____10332 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___105_10346 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___105_10346.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___105_10346.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___105_10346.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___105_10346.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___105_10346.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___105_10346.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10332)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10319  in
                            mk1 uu____10318  in
                          ((M t2), uu____10302, uu____10317)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10356 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____10356  in
      let uu____10357 = check env e mn  in
      match uu____10357 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10373 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10395 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____10395  in
      let uu____10396 = check env e mn  in
      match uu____10396 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10412 -> failwith "[check_m]: impossible"

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
        (let uu____10442 =
           let uu____10443 = is_C c  in Prims.op_Negation uu____10443  in
         if uu____10442 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____10453 =
           let uu____10454 = FStar_Syntax_Subst.compress c  in
           uu____10454.FStar_Syntax_Syntax.n  in
         match uu____10453 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____10479 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____10479 with
              | (wp_head,wp_args) ->
                  ((let uu____10517 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____10531 =
                           let uu____10532 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____10532
                            in
                         Prims.op_Negation uu____10531)
                       in
                    if uu____10517 then failwith "mismatch" else ());
                   (let uu____10540 =
                      let uu____10541 =
                        let uu____10556 =
                          FStar_List.map2
                            (fun uu____10586  ->
                               fun uu____10587  ->
                                 match (uu____10586, uu____10587) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____10626 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____10626
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____10629 =
                                           let uu____10634 =
                                             let uu____10635 =
                                               print_implicit q  in
                                             let uu____10636 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %b %b\n"
                                               uu____10635 uu____10636
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____10634)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____10629)
                                      else ();
                                      (let uu____10638 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____10638, q)))) args wp_args
                           in
                        (head1, uu____10556)  in
                      FStar_Syntax_Syntax.Tm_app uu____10541  in
                    mk1 uu____10540)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____10674 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____10674 with
              | (binders_orig,comp1) ->
                  let uu____10681 =
                    let uu____10696 =
                      FStar_List.map
                        (fun uu____10730  ->
                           match uu____10730 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____10750 = is_C h  in
                               if uu____10750
                               then
                                 let w' =
                                   let uu____10762 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____10762
                                    in
                                 let uu____10763 =
                                   let uu____10770 =
                                     let uu____10777 =
                                       let uu____10782 =
                                         let uu____10783 =
                                           let uu____10784 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____10784  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____10783
                                          in
                                       (uu____10782, q)  in
                                     [uu____10777]  in
                                   (w', q) :: uu____10770  in
                                 (w', uu____10763)
                               else
                                 (let x =
                                    let uu____10805 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____10805
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____10696  in
                  (match uu____10681 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____10860 =
                           let uu____10863 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____10863
                            in
                         FStar_Syntax_Subst.subst_comp uu____10860 comp1  in
                       let app =
                         let uu____10867 =
                           let uu____10868 =
                             let uu____10883 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____10900 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____10901 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____10900, uu____10901)) bvs
                                in
                             (wp, uu____10883)  in
                           FStar_Syntax_Syntax.Tm_app uu____10868  in
                         mk1 uu____10867  in
                       let comp3 =
                         let uu____10913 = type_of_comp comp2  in
                         let uu____10914 = is_monadic_comp comp2  in
                         trans_G env uu____10913 uu____10914 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____10916,uu____10917) ->
             trans_F_ env e wp
         | uu____10958 -> failwith "impossible trans_F_")

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
            let uu____10963 =
              let uu____10964 = star_type' env h  in
              let uu____10967 =
                let uu____10976 =
                  let uu____10983 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____10983)  in
                [uu____10976]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____10964;
                FStar_Syntax_Syntax.effect_args = uu____10967;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____10963
          else
            (let uu____10999 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____10999)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____11018 = n env.env t  in star_type' env uu____11018
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____11037 = n env.env t  in check_n env uu____11037
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____11053 = n env.env c  in
        let uu____11054 = n env.env wp  in
        trans_F_ env uu____11053 uu____11054
  