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
              let uu___343_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___343_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___343_123.FStar_Syntax_Syntax.index);
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
                  (fun uu____418  ->
                     match uu____418 with
                     | (t,b) ->
                         let uu____429 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____429))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____462 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____462))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____487 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____487)
                 in
              let uu____488 =
                let uu____505 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____529 =
                        let uu____532 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____532  in
                      FStar_Syntax_Util.arrow gamma uu____529  in
                    let uu____533 =
                      let uu____534 =
                        let uu____541 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____546 =
                          let uu____553 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____553]  in
                        uu____541 :: uu____546  in
                      FStar_List.append binders uu____534  in
                    FStar_Syntax_Util.abs uu____533 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____574 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____575 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____574, uu____575)  in
                match uu____505 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____615 =
                        let uu____616 =
                          let uu____631 =
                            let uu____640 =
                              FStar_List.map
                                (fun uu____660  ->
                                   match uu____660 with
                                   | (bv,uu____670) ->
                                       let uu____671 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____672 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____671, uu____672)) binders
                               in
                            let uu____673 =
                              let uu____680 =
                                let uu____685 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____686 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____685, uu____686)  in
                              let uu____687 =
                                let uu____694 =
                                  let uu____699 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____699)  in
                                [uu____694]  in
                              uu____680 :: uu____687  in
                            FStar_List.append uu____640 uu____673  in
                          (fv, uu____631)  in
                        FStar_Syntax_Syntax.Tm_app uu____616  in
                      mk1 uu____615  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____488 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____768 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____768
                       in
                    let ret1 =
                      let uu____772 =
                        let uu____773 =
                          let uu____776 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____776  in
                        FStar_Syntax_Util.residual_tot uu____773  in
                      FStar_Pervasives_Native.Some uu____772  in
                    let body =
                      let uu____780 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____780 ret1  in
                    let uu____783 =
                      let uu____784 = mk_all_implicit binders  in
                      let uu____791 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____784 uu____791  in
                    FStar_Syntax_Util.abs uu____783 body ret1  in
                  let c_pure1 =
                    let uu____819 = mk_lid "pure"  in
                    register env1 uu____819 c_pure  in
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
                      let uu____826 =
                        let uu____827 =
                          let uu____828 =
                            let uu____835 =
                              let uu____840 =
                                let uu____841 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____841
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____840  in
                            [uu____835]  in
                          let uu____850 =
                            let uu____853 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____853  in
                          FStar_Syntax_Util.arrow uu____828 uu____850  in
                        mk_gctx uu____827  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____826
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
                        let uu____971 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____971  in
                      FStar_Syntax_Util.arrow uu____947 uu____968  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____974 =
                        let uu____975 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____975  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____974
                       in
                    let ret1 =
                      let uu____979 =
                        let uu____980 =
                          let uu____983 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____983  in
                        FStar_Syntax_Util.residual_tot uu____980  in
                      FStar_Pervasives_Native.Some uu____979  in
                    let uu____984 =
                      let uu____985 = mk_all_implicit binders  in
                      let uu____992 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____985 uu____992  in
                    let uu____1027 =
                      let uu____1030 =
                        let uu____1039 =
                          let uu____1042 =
                            let uu____1043 =
                              let uu____1052 =
                                let uu____1055 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1055]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1052
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1043  in
                          let uu____1062 =
                            let uu____1065 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1065]  in
                          uu____1042 :: uu____1062  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1039
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1030  in
                    FStar_Syntax_Util.abs uu____984 uu____1027 ret1  in
                  let c_lift11 =
                    let uu____1073 = mk_lid "lift1"  in
                    register env1 uu____1073 c_lift1  in
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
                      let uu____1083 =
                        let uu____1090 =
                          let uu____1095 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1095  in
                        let uu____1096 =
                          let uu____1103 =
                            let uu____1108 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1108  in
                          [uu____1103]  in
                        uu____1090 :: uu____1096  in
                      let uu____1121 =
                        let uu____1124 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1124  in
                      FStar_Syntax_Util.arrow uu____1083 uu____1121  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1127 =
                        let uu____1128 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1128  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1127
                       in
                    let a2 =
                      let uu____1130 =
                        let uu____1131 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1131  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1130
                       in
                    let ret1 =
                      let uu____1135 =
                        let uu____1136 =
                          let uu____1139 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1139  in
                        FStar_Syntax_Util.residual_tot uu____1136  in
                      FStar_Pervasives_Native.Some uu____1135  in
                    let uu____1140 =
                      let uu____1141 = mk_all_implicit binders  in
                      let uu____1148 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1141 uu____1148  in
                    let uu____1191 =
                      let uu____1194 =
                        let uu____1203 =
                          let uu____1206 =
                            let uu____1207 =
                              let uu____1216 =
                                let uu____1219 =
                                  let uu____1220 =
                                    let uu____1229 =
                                      let uu____1232 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1232]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1229
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1220
                                   in
                                let uu____1239 =
                                  let uu____1242 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1242]  in
                                uu____1219 :: uu____1239  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1216
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1207  in
                          let uu____1249 =
                            let uu____1252 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1252]  in
                          uu____1206 :: uu____1249  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1203
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1194  in
                    FStar_Syntax_Util.abs uu____1140 uu____1191 ret1  in
                  let c_lift21 =
                    let uu____1260 = mk_lid "lift2"  in
                    register env1 uu____1260 c_lift2  in
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
                      let uu____1269 =
                        let uu____1276 =
                          let uu____1281 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1281  in
                        [uu____1276]  in
                      let uu____1290 =
                        let uu____1293 =
                          let uu____1294 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1294  in
                        FStar_Syntax_Syntax.mk_Total uu____1293  in
                      FStar_Syntax_Util.arrow uu____1269 uu____1290  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1299 =
                        let uu____1300 =
                          let uu____1303 =
                            let uu____1304 =
                              let uu____1311 =
                                let uu____1316 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1316
                                 in
                              [uu____1311]  in
                            let uu____1325 =
                              let uu____1328 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1328  in
                            FStar_Syntax_Util.arrow uu____1304 uu____1325  in
                          mk_ctx uu____1303  in
                        FStar_Syntax_Util.residual_tot uu____1300  in
                      FStar_Pervasives_Native.Some uu____1299  in
                    let e1 =
                      let uu____1330 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1330
                       in
                    let body =
                      let uu____1334 =
                        let uu____1335 =
                          let uu____1342 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1342]  in
                        FStar_List.append gamma uu____1335  in
                      let uu____1359 =
                        let uu____1362 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1365 =
                          let uu____1374 =
                            let uu____1375 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1375  in
                          let uu____1376 = args_of_binders1 gamma  in
                          uu____1374 :: uu____1376  in
                        FStar_Syntax_Util.mk_app uu____1362 uu____1365  in
                      FStar_Syntax_Util.abs uu____1334 uu____1359 ret1  in
                    let uu____1379 =
                      let uu____1380 = mk_all_implicit binders  in
                      let uu____1387 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1380 uu____1387  in
                    FStar_Syntax_Util.abs uu____1379 body ret1  in
                  let c_push1 =
                    let uu____1419 = mk_lid "push"  in
                    register env1 uu____1419 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1441 =
                        let uu____1442 =
                          let uu____1457 = args_of_binders1 binders  in
                          (c, uu____1457)  in
                        FStar_Syntax_Syntax.Tm_app uu____1442  in
                      mk1 uu____1441
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1481 =
                        let uu____1482 =
                          let uu____1489 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1494 =
                            let uu____1501 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1501]  in
                          uu____1489 :: uu____1494  in
                        let uu____1518 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1482 uu____1518  in
                      FStar_Syntax_Syntax.mk_Total uu____1481  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1522 =
                      let uu____1523 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1523  in
                    let uu____1534 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1538 =
                        let uu____1541 =
                          let uu____1550 =
                            let uu____1553 =
                              let uu____1554 =
                                let uu____1563 =
                                  let uu____1570 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1570  in
                                [uu____1563]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1554  in
                            [uu____1553]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1550
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1541  in
                      FStar_Syntax_Util.ascribe uu____1538
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1522 uu____1534
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1608 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1608 wp_if_then_else  in
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
                      let uu____1621 =
                        let uu____1630 =
                          let uu____1633 =
                            let uu____1634 =
                              let uu____1643 =
                                let uu____1646 =
                                  let uu____1647 =
                                    let uu____1656 =
                                      let uu____1663 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1663
                                       in
                                    [uu____1656]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1647
                                   in
                                [uu____1646]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1643
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1634  in
                          let uu____1682 =
                            let uu____1685 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1685]  in
                          uu____1633 :: uu____1682  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1630
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1621  in
                    let uu____1692 =
                      let uu____1693 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1693  in
                    FStar_Syntax_Util.abs uu____1692 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1705 = mk_lid "wp_assert"  in
                    register env1 uu____1705 wp_assert  in
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
                      let uu____1718 =
                        let uu____1727 =
                          let uu____1730 =
                            let uu____1731 =
                              let uu____1740 =
                                let uu____1743 =
                                  let uu____1744 =
                                    let uu____1753 =
                                      let uu____1760 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1760
                                       in
                                    [uu____1753]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1744
                                   in
                                [uu____1743]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1740
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1731  in
                          let uu____1779 =
                            let uu____1782 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1782]  in
                          uu____1730 :: uu____1779  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1727
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1718  in
                    let uu____1789 =
                      let uu____1790 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1790  in
                    FStar_Syntax_Util.abs uu____1789 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1802 = mk_lid "wp_assume"  in
                    register env1 uu____1802 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1813 =
                        let uu____1820 =
                          let uu____1825 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1825  in
                        [uu____1820]  in
                      let uu____1834 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1813 uu____1834  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1841 =
                        let uu____1850 =
                          let uu____1853 =
                            let uu____1854 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1854  in
                          let uu____1869 =
                            let uu____1872 =
                              let uu____1873 =
                                let uu____1882 =
                                  let uu____1885 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1885]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1882
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1873  in
                            [uu____1872]  in
                          uu____1853 :: uu____1869  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1850
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1841  in
                    let uu____1898 =
                      let uu____1899 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1899  in
                    FStar_Syntax_Util.abs uu____1898 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1911 = mk_lid "wp_close"  in
                    register env1 uu____1911 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1921 =
                      let uu____1922 =
                        let uu____1923 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1923
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1922  in
                    FStar_Pervasives_Native.Some uu____1921  in
                  let mk_forall1 x body =
                    let uu____1935 =
                      let uu____1942 =
                        let uu____1943 =
                          let uu____1958 =
                            let uu____1967 =
                              let uu____1974 =
                                let uu____1975 =
                                  let uu____1976 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1976]  in
                                FStar_Syntax_Util.abs uu____1975 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1974  in
                            [uu____1967]  in
                          (FStar_Syntax_Util.tforall, uu____1958)  in
                        FStar_Syntax_Syntax.Tm_app uu____1943  in
                      FStar_Syntax_Syntax.mk uu____1942  in
                    uu____1935 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____2024 =
                      let uu____2025 = FStar_Syntax_Subst.compress t  in
                      uu____2025.FStar_Syntax_Syntax.n  in
                    match uu____2024 with
                    | FStar_Syntax_Syntax.Tm_type uu____2028 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2054  ->
                              match uu____2054 with
                              | (b,uu____2060) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2061 -> true  in
                  let rec is_monotonic t =
                    let uu____2072 =
                      let uu____2073 = FStar_Syntax_Subst.compress t  in
                      uu____2073.FStar_Syntax_Syntax.n  in
                    match uu____2072 with
                    | FStar_Syntax_Syntax.Tm_type uu____2076 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2102  ->
                              match uu____2102 with
                              | (b,uu____2108) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2109 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____2183 =
                      let uu____2184 = FStar_Syntax_Subst.compress t1  in
                      uu____2184.FStar_Syntax_Syntax.n  in
                    match uu____2183 with
                    | FStar_Syntax_Syntax.Tm_type uu____2189 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2192);
                                      FStar_Syntax_Syntax.pos = uu____2193;
                                      FStar_Syntax_Syntax.vars = uu____2194;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2228 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2228
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2235 =
                              let uu____2238 =
                                let uu____2247 =
                                  let uu____2254 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2254  in
                                [uu____2247]  in
                              FStar_Syntax_Util.mk_app x uu____2238  in
                            let uu____2267 =
                              let uu____2270 =
                                let uu____2279 =
                                  let uu____2286 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2286  in
                                [uu____2279]  in
                              FStar_Syntax_Util.mk_app y uu____2270  in
                            mk_rel1 b uu____2235 uu____2267  in
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
                             let uu____2303 =
                               let uu____2306 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2309 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2306 uu____2309  in
                             let uu____2312 =
                               let uu____2315 =
                                 let uu____2318 =
                                   let uu____2327 =
                                     let uu____2334 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2334
                                      in
                                   [uu____2327]  in
                                 FStar_Syntax_Util.mk_app x uu____2318  in
                               let uu____2347 =
                                 let uu____2350 =
                                   let uu____2359 =
                                     let uu____2366 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2366
                                      in
                                   [uu____2359]  in
                                 FStar_Syntax_Util.mk_app y uu____2350  in
                               mk_rel1 b uu____2315 uu____2347  in
                             FStar_Syntax_Util.mk_imp uu____2303 uu____2312
                              in
                           let uu____2379 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2379)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2382);
                                      FStar_Syntax_Syntax.pos = uu____2383;
                                      FStar_Syntax_Syntax.vars = uu____2384;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2418 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2418
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2425 =
                              let uu____2428 =
                                let uu____2437 =
                                  let uu____2444 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2444  in
                                [uu____2437]  in
                              FStar_Syntax_Util.mk_app x uu____2428  in
                            let uu____2457 =
                              let uu____2460 =
                                let uu____2469 =
                                  let uu____2476 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2476  in
                                [uu____2469]  in
                              FStar_Syntax_Util.mk_app y uu____2460  in
                            mk_rel1 b uu____2425 uu____2457  in
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
                             let uu____2493 =
                               let uu____2496 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2499 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2496 uu____2499  in
                             let uu____2502 =
                               let uu____2505 =
                                 let uu____2508 =
                                   let uu____2517 =
                                     let uu____2524 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2524
                                      in
                                   [uu____2517]  in
                                 FStar_Syntax_Util.mk_app x uu____2508  in
                               let uu____2537 =
                                 let uu____2540 =
                                   let uu____2549 =
                                     let uu____2556 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2556
                                      in
                                   [uu____2549]  in
                                 FStar_Syntax_Util.mk_app y uu____2540  in
                               mk_rel1 b uu____2505 uu____2537  in
                             FStar_Syntax_Util.mk_imp uu____2493 uu____2502
                              in
                           let uu____2569 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2569)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___344_2600 = t1  in
                          let uu____2601 =
                            let uu____2602 =
                              let uu____2615 =
                                let uu____2618 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2618  in
                              ([binder], uu____2615)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2602  in
                          {
                            FStar_Syntax_Syntax.n = uu____2601;
                            FStar_Syntax_Syntax.pos =
                              (uu___344_2600.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___344_2600.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2635 ->
                        failwith "unhandled arrow"
                    | uu____2650 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____2685 =
                        let uu____2686 = FStar_Syntax_Subst.compress t1  in
                        uu____2686.FStar_Syntax_Syntax.n  in
                      match uu____2685 with
                      | FStar_Syntax_Syntax.Tm_type uu____2689 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2712 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2712
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2731 =
                                let uu____2732 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2732 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2731
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2753 =
                            let uu____2764 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2780  ->
                                     match uu____2780 with
                                     | (t2,q) ->
                                         let uu____2793 = project i x  in
                                         let uu____2796 = project i y  in
                                         mk_stronger t2 uu____2793 uu____2796)
                                args
                               in
                            match uu____2764 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2753 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2849);
                                      FStar_Syntax_Syntax.pos = uu____2850;
                                      FStar_Syntax_Syntax.vars = uu____2851;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2889  ->
                                   match uu____2889 with
                                   | (bv,q) ->
                                       let uu____2896 =
                                         let uu____2897 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2897  in
                                       FStar_Syntax_Syntax.gen_bv uu____2896
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2904 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2904) bvs
                             in
                          let body =
                            let uu____2906 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2909 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2906 uu____2909  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2918);
                                      FStar_Syntax_Syntax.pos = uu____2919;
                                      FStar_Syntax_Syntax.vars = uu____2920;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2958  ->
                                   match uu____2958 with
                                   | (bv,q) ->
                                       let uu____2965 =
                                         let uu____2966 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2966  in
                                       FStar_Syntax_Syntax.gen_bv uu____2965
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2973 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2973) bvs
                             in
                          let body =
                            let uu____2975 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2978 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2975 uu____2978  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2985 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2987 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2990 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____2993 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2987 uu____2990 uu____2993  in
                    let uu____2996 =
                      let uu____2997 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____2997  in
                    FStar_Syntax_Util.abs uu____2996 body ret_tot_type  in
                  let stronger1 =
                    let uu____3025 = mk_lid "stronger"  in
                    register env1 uu____3025 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3031 = FStar_Util.prefix gamma  in
                    match uu____3031 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____3080 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3080
                             in
                          let uu____3083 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____3083 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3093 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____3093  in
                              let guard_free1 =
                                let uu____3103 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____3103  in
                              let pat =
                                let uu____3107 =
                                  let uu____3116 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____3116]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3107
                                 in
                              let pattern_guarded_body =
                                let uu____3138 =
                                  let uu____3139 =
                                    let uu____3146 =
                                      let uu____3147 =
                                        let uu____3158 =
                                          let uu____3167 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____3167]  in
                                        [uu____3158]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3147
                                       in
                                    (body, uu____3146)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____3139  in
                                mk1 uu____3138  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3204 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____3212 =
                            let uu____3215 =
                              let uu____3216 =
                                let uu____3219 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____3222 =
                                  let uu____3231 = args_of_binders1 wp_args
                                     in
                                  let uu____3234 =
                                    let uu____3237 =
                                      let uu____3238 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____3238
                                       in
                                    [uu____3237]  in
                                  FStar_List.append uu____3231 uu____3234  in
                                FStar_Syntax_Util.mk_app uu____3219
                                  uu____3222
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____3216  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3215
                             in
                          FStar_Syntax_Util.abs gamma uu____3212
                            ret_gtot_type
                           in
                        let uu____3239 =
                          let uu____3240 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____3240  in
                        FStar_Syntax_Util.abs uu____3239 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____3252 = mk_lid "wp_ite"  in
                    register env1 uu____3252 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____3258 = FStar_Util.prefix gamma  in
                    match uu____3258 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____3301 =
                            let uu____3302 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____3307 =
                              let uu____3316 =
                                let uu____3323 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____3323  in
                              [uu____3316]  in
                            FStar_Syntax_Util.mk_app uu____3302 uu____3307
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3301
                           in
                        let uu____3336 =
                          let uu____3337 =
                            let uu____3344 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____3344 gamma  in
                          FStar_List.append binders uu____3337  in
                        FStar_Syntax_Util.abs uu____3336 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____3360 = mk_lid "null_wp"  in
                    register env1 uu____3360 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____3371 =
                        let uu____3380 =
                          let uu____3383 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____3384 =
                            let uu____3387 =
                              let uu____3388 =
                                let uu____3397 =
                                  let uu____3404 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____3404  in
                                [uu____3397]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3388
                               in
                            let uu____3417 =
                              let uu____3420 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____3420]  in
                            uu____3387 :: uu____3417  in
                          uu____3383 :: uu____3384  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3380
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____3371  in
                    let uu____3427 =
                      let uu____3428 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____3428  in
                    FStar_Syntax_Util.abs uu____3427 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____3440 = mk_lid "wp_trivial"  in
                    register env1 uu____3440 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____3445 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____3445
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____3452 =
                      let uu____3453 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____3453  in
                    let uu____3501 =
                      let uu___345_3502 = ed  in
                      let uu____3503 =
                        let uu____3504 = c wp_if_then_else2  in
                        ([], uu____3504)  in
                      let uu____3511 =
                        let uu____3512 = c wp_ite2  in ([], uu____3512)  in
                      let uu____3519 =
                        let uu____3520 = c stronger2  in ([], uu____3520)  in
                      let uu____3527 =
                        let uu____3528 = c wp_close2  in ([], uu____3528)  in
                      let uu____3535 =
                        let uu____3536 = c wp_assert2  in ([], uu____3536)
                         in
                      let uu____3543 =
                        let uu____3544 = c wp_assume2  in ([], uu____3544)
                         in
                      let uu____3551 =
                        let uu____3552 = c null_wp2  in ([], uu____3552)  in
                      let uu____3559 =
                        let uu____3560 = c wp_trivial2  in ([], uu____3560)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___345_3502.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___345_3502.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___345_3502.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___345_3502.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___345_3502.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___345_3502.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___345_3502.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3503;
                        FStar_Syntax_Syntax.ite_wp = uu____3511;
                        FStar_Syntax_Syntax.stronger = uu____3519;
                        FStar_Syntax_Syntax.close_wp = uu____3527;
                        FStar_Syntax_Syntax.assert_p = uu____3535;
                        FStar_Syntax_Syntax.assume_p = uu____3543;
                        FStar_Syntax_Syntax.null_wp = uu____3551;
                        FStar_Syntax_Syntax.trivial = uu____3559;
                        FStar_Syntax_Syntax.repr =
                          (uu___345_3502.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___345_3502.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___345_3502.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___345_3502.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___345_3502.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____3452, uu____3501)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___346_3582 = dmff_env  in
      {
        env = env';
        subst = (uu___346_3582.subst);
        tc_const = (uu___346_3582.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____3599 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____3613 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___332_3625  ->
    match uu___332_3625 with
    | FStar_Syntax_Syntax.Total (t,uu____3627) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___331_3640  ->
                match uu___331_3640 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3641 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____3643 =
          let uu____3644 =
            let uu____3645 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3645
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3644  in
        failwith uu____3643
    | FStar_Syntax_Syntax.GTotal uu____3646 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___333_3659  ->
    match uu___333_3659 with
    | N t ->
        let uu____3661 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____3661
    | M t ->
        let uu____3663 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____3663
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3669,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____3671;
                      FStar_Syntax_Syntax.vars = uu____3672;_})
        -> nm_of_comp n2
    | uu____3689 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____3699 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3699 with | M uu____3700 -> true | N uu____3701 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3707 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3721 =
        let uu____3728 =
          let uu____3733 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3733  in
        [uu____3728]  in
      let uu____3746 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3721 uu____3746  in
    let uu____3749 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3749
  
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
        let uu____3790 =
          let uu____3791 =
            let uu____3804 =
              let uu____3811 =
                let uu____3816 =
                  let uu____3817 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____3817  in
                let uu____3818 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____3816, uu____3818)  in
              [uu____3811]  in
            let uu____3827 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____3804, uu____3827)  in
          FStar_Syntax_Syntax.Tm_arrow uu____3791  in
        mk1 uu____3790

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3865) ->
          let binders1 =
            FStar_List.map
              (fun uu____3901  ->
                 match uu____3901 with
                 | (bv,aqual) ->
                     let uu____3912 =
                       let uu___347_3913 = bv  in
                       let uu____3914 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___347_3913.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___347_3913.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3914
                       }  in
                     (uu____3912, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3917,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3919);
                             FStar_Syntax_Syntax.pos = uu____3920;
                             FStar_Syntax_Syntax.vars = uu____3921;_})
               ->
               let uu____3946 =
                 let uu____3947 =
                   let uu____3960 =
                     let uu____3963 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3963  in
                   (binders1, uu____3960)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3947  in
               mk1 uu____3946
           | uu____3972 ->
               let uu____3973 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3973 with
                | N hn ->
                    let uu____3975 =
                      let uu____3976 =
                        let uu____3989 =
                          let uu____3992 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3992  in
                        (binders1, uu____3989)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3976  in
                    mk1 uu____3975
                | M a ->
                    let uu____4002 =
                      let uu____4003 =
                        let uu____4016 =
                          let uu____4023 =
                            let uu____4030 =
                              let uu____4035 =
                                let uu____4036 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____4036  in
                              let uu____4037 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____4035, uu____4037)  in
                            [uu____4030]  in
                          FStar_List.append binders1 uu____4023  in
                        let uu____4050 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____4016, uu____4050)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____4003  in
                    mk1 uu____4002))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4132 = f x  in
                    FStar_Util.string_builder_append strb uu____4132);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4139 = f x1  in
                         FStar_Util.string_builder_append strb uu____4139))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____4141 =
              let uu____4146 =
                let uu____4147 = FStar_Syntax_Print.term_to_string t2  in
                let uu____4148 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4147 uu____4148
                 in
              (FStar_Errors.Warning_DependencyFound, uu____4146)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4141  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____4164 =
              let uu____4165 = FStar_Syntax_Subst.compress ty  in
              uu____4165.FStar_Syntax_Syntax.n  in
            match uu____4164 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____4186 =
                  let uu____4187 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____4187  in
                if uu____4186
                then false
                else
                  (try
                     (fun uu___349_4198  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4221 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____4221 s  in
                              let uu____4224 =
                                let uu____4225 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____4225  in
                              if uu____4224
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____4228 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____4228 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____4250  ->
                                          match uu____4250 with
                                          | (bv,uu____4260) ->
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
            | uu____4274 ->
                ((let uu____4276 =
                    let uu____4281 =
                      let uu____4282 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4282
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4281)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4276);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____4293 =
              let uu____4294 = FStar_Syntax_Subst.compress head2  in
              uu____4294.FStar_Syntax_Syntax.n  in
            match uu____4293 with
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
                  (let uu____4299 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____4299)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4301 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____4301 with
                 | ((uu____4310,ty),uu____4312) ->
                     let uu____4317 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____4317
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.env t1
                          in
                       let uu____4325 =
                         let uu____4326 = FStar_Syntax_Subst.compress res  in
                         uu____4326.FStar_Syntax_Syntax.n  in
                       (match uu____4325 with
                        | FStar_Syntax_Syntax.Tm_app uu____4329 -> true
                        | uu____4344 ->
                            ((let uu____4346 =
                                let uu____4351 =
                                  let uu____4352 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____4352
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____4351)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____4346);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____4354 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4355 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4357) ->
                is_valid_application t2
            | uu____4362 -> false  in
          let uu____4363 = is_valid_application head1  in
          if uu____4363
          then
            let uu____4364 =
              let uu____4365 =
                let uu____4380 =
                  FStar_List.map
                    (fun uu____4403  ->
                       match uu____4403 with
                       | (t2,qual) ->
                           let uu____4420 = star_type' env t2  in
                           (uu____4420, qual)) args
                   in
                (head1, uu____4380)  in
              FStar_Syntax_Syntax.Tm_app uu____4365  in
            mk1 uu____4364
          else
            (let uu____4432 =
               let uu____4437 =
                 let uu____4438 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____4438
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____4437)  in
             FStar_Errors.raise_err uu____4432)
      | FStar_Syntax_Syntax.Tm_bvar uu____4439 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____4440 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____4441 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____4442 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____4466 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____4466 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___350_4474 = env  in
                 let uu____4475 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____4475;
                   subst = (uu___350_4474.subst);
                   tc_const = (uu___350_4474.tc_const)
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
               ((let uu___351_4497 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___351_4497.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___351_4497.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____4504 =
            let uu____4505 =
              let uu____4512 = star_type' env t2  in (uu____4512, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____4505  in
          mk1 uu____4504
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____4564 =
            let uu____4565 =
              let uu____4592 = star_type' env e  in
              let uu____4595 =
                let uu____4612 =
                  let uu____4621 = star_type' env t2  in
                  FStar_Util.Inl uu____4621  in
                (uu____4612, FStar_Pervasives_Native.None)  in
              (uu____4592, uu____4595, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4565  in
          mk1 uu____4564
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____4709 =
            let uu____4710 =
              let uu____4737 = star_type' env e  in
              let uu____4740 =
                let uu____4757 =
                  let uu____4766 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4766  in
                (uu____4757, FStar_Pervasives_Native.None)  in
              (uu____4737, uu____4740, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____4710  in
          mk1 uu____4709
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4807,(uu____4808,FStar_Pervasives_Native.Some uu____4809),uu____4810)
          ->
          let uu____4859 =
            let uu____4864 =
              let uu____4865 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4865
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4864)  in
          FStar_Errors.raise_err uu____4859
      | FStar_Syntax_Syntax.Tm_refine uu____4866 ->
          let uu____4873 =
            let uu____4878 =
              let uu____4879 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4879
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4878)  in
          FStar_Errors.raise_err uu____4873
      | FStar_Syntax_Syntax.Tm_uinst uu____4880 ->
          let uu____4887 =
            let uu____4892 =
              let uu____4893 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4893
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4892)  in
          FStar_Errors.raise_err uu____4887
      | FStar_Syntax_Syntax.Tm_quoted uu____4894 ->
          let uu____4901 =
            let uu____4906 =
              let uu____4907 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4907
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4906)  in
          FStar_Errors.raise_err uu____4901
      | FStar_Syntax_Syntax.Tm_constant uu____4908 ->
          let uu____4909 =
            let uu____4914 =
              let uu____4915 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4915
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4914)  in
          FStar_Errors.raise_err uu____4909
      | FStar_Syntax_Syntax.Tm_match uu____4916 ->
          let uu____4939 =
            let uu____4944 =
              let uu____4945 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4945
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4944)  in
          FStar_Errors.raise_err uu____4939
      | FStar_Syntax_Syntax.Tm_let uu____4946 ->
          let uu____4959 =
            let uu____4964 =
              let uu____4965 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4965
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4964)  in
          FStar_Errors.raise_err uu____4959
      | FStar_Syntax_Syntax.Tm_uvar uu____4966 ->
          let uu____4979 =
            let uu____4984 =
              let uu____4985 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4985
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4984)  in
          FStar_Errors.raise_err uu____4979
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4986 =
            let uu____4991 =
              let uu____4992 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4992
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4991)  in
          FStar_Errors.raise_err uu____4986
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4994 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4994
      | FStar_Syntax_Syntax.Tm_delayed uu____4997 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___335_5026  ->
    match uu___335_5026 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___334_5033  ->
                match uu___334_5033 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____5034 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____5040 =
      let uu____5041 = FStar_Syntax_Subst.compress t  in
      uu____5041.FStar_Syntax_Syntax.n  in
    match uu____5040 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____5067 =
            let uu____5068 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____5068  in
          is_C uu____5067  in
        if r
        then
          ((let uu____5084 =
              let uu____5085 =
                FStar_List.for_all
                  (fun uu____5093  ->
                     match uu____5093 with | (h,uu____5099) -> is_C h) args
                 in
              Prims.op_Negation uu____5085  in
            if uu____5084 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____5103 =
              let uu____5104 =
                FStar_List.for_all
                  (fun uu____5113  ->
                     match uu____5113 with
                     | (h,uu____5119) ->
                         let uu____5120 = is_C h  in
                         Prims.op_Negation uu____5120) args
                 in
              Prims.op_Negation uu____5104  in
            if uu____5103 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____5140 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____5140 with
         | M t1 ->
             ((let uu____5143 = is_C t1  in
               if uu____5143 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____5147) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5153) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____5159,uu____5160) -> is_C t1
    | uu____5201 -> false
  
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
          let uu____5234 =
            let uu____5235 =
              let uu____5250 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____5253 =
                let uu____5262 =
                  let uu____5269 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____5269)  in
                [uu____5262]  in
              (uu____5250, uu____5253)  in
            FStar_Syntax_Syntax.Tm_app uu____5235  in
          mk1 uu____5234  in
        let uu____5294 =
          let uu____5295 = FStar_Syntax_Syntax.mk_binder p  in [uu____5295]
           in
        FStar_Syntax_Util.abs uu____5294 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___336_5312  ->
    match uu___336_5312 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5313 -> false
  
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
        let return_if uu____5548 =
          match uu____5548 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____5585 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____5587 =
                       let uu____5588 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____5588  in
                     Prims.op_Negation uu____5587)
                   in
                if uu____5585
                then
                  let uu____5589 =
                    let uu____5594 =
                      let uu____5595 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____5596 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____5597 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____5595 uu____5596 uu____5597
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____5594)  in
                  FStar_Errors.raise_err uu____5589
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____5618 = mk_return env t1 s_e  in
                     ((M t1), uu____5618, u_e)))
               | (M t1,N t2) ->
                   let uu____5625 =
                     let uu____5630 =
                       let uu____5631 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____5632 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____5633 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____5631 uu____5632 uu____5633
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____5630)
                      in
                   FStar_Errors.raise_err uu____5625)
           in
        let ensure_m env1 e2 =
          let strip_m uu___337_5682 =
            match uu___337_5682 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____5698 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____5718 =
                let uu____5723 =
                  let uu____5724 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____5724
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____5723)  in
              FStar_Errors.raise_error uu____5718 e2.FStar_Syntax_Syntax.pos
          | M uu____5731 ->
              let uu____5732 = check env1 e2 context_nm  in
              strip_m uu____5732
           in
        let uu____5739 =
          let uu____5740 = FStar_Syntax_Subst.compress e  in
          uu____5740.FStar_Syntax_Syntax.n  in
        match uu____5739 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5749 ->
            let uu____5750 = infer env e  in return_if uu____5750
        | FStar_Syntax_Syntax.Tm_name uu____5757 ->
            let uu____5758 = infer env e  in return_if uu____5758
        | FStar_Syntax_Syntax.Tm_fvar uu____5765 ->
            let uu____5766 = infer env e  in return_if uu____5766
        | FStar_Syntax_Syntax.Tm_abs uu____5773 ->
            let uu____5790 = infer env e  in return_if uu____5790
        | FStar_Syntax_Syntax.Tm_constant uu____5797 ->
            let uu____5798 = infer env e  in return_if uu____5798
        | FStar_Syntax_Syntax.Tm_quoted uu____5805 ->
            let uu____5812 = infer env e  in return_if uu____5812
        | FStar_Syntax_Syntax.Tm_app uu____5819 ->
            let uu____5834 = infer env e  in return_if uu____5834
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5842 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5842 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5904) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5910) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5916,uu____5917) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5958 ->
            let uu____5971 =
              let uu____5972 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5972  in
            failwith uu____5971
        | FStar_Syntax_Syntax.Tm_type uu____5979 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5986 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6005 ->
            let uu____6012 =
              let uu____6013 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6013  in
            failwith uu____6012
        | FStar_Syntax_Syntax.Tm_uvar uu____6020 ->
            let uu____6033 =
              let uu____6034 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6034  in
            failwith uu____6033
        | FStar_Syntax_Syntax.Tm_delayed uu____6041 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____6070 =
              let uu____6071 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6071  in
            failwith uu____6070

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
      let uu____6099 =
        let uu____6100 = FStar_Syntax_Subst.compress e  in
        uu____6100.FStar_Syntax_Syntax.n  in
      match uu____6099 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6118 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____6118
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6165;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____6166;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6172 =
                  let uu___352_6173 = rc  in
                  let uu____6174 =
                    let uu____6179 =
                      let uu____6182 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____6182  in
                    FStar_Pervasives_Native.Some uu____6179  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___352_6173.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6174;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___352_6173.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____6172
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___353_6194 = env  in
            let uu____6195 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____6195;
              subst = (uu___353_6194.subst);
              tc_const = (uu___353_6194.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____6215  ->
                 match uu____6215 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___354_6228 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___354_6228.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___354_6228.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____6229 =
            FStar_List.fold_left
              (fun uu____6258  ->
                 fun uu____6259  ->
                   match (uu____6258, uu____6259) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____6307 = is_C c  in
                       if uu____6307
                       then
                         let xw =
                           let uu____6315 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____6315
                            in
                         let x =
                           let uu___355_6317 = bv  in
                           let uu____6318 =
                             let uu____6321 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____6321  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___355_6317.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___355_6317.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____6318
                           }  in
                         let env3 =
                           let uu___356_6323 = env2  in
                           let uu____6324 =
                             let uu____6327 =
                               let uu____6328 =
                                 let uu____6335 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____6335)  in
                               FStar_Syntax_Syntax.NT uu____6328  in
                             uu____6327 :: (env2.subst)  in
                           {
                             env = (uu___356_6323.env);
                             subst = uu____6324;
                             tc_const = (uu___356_6323.tc_const)
                           }  in
                         let uu____6340 =
                           let uu____6343 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____6344 =
                             let uu____6347 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____6347 :: acc  in
                           uu____6343 :: uu____6344  in
                         (env3, uu____6340)
                       else
                         (let x =
                            let uu___357_6352 = bv  in
                            let uu____6353 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___357_6352.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___357_6352.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____6353
                            }  in
                          let uu____6356 =
                            let uu____6359 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____6359 :: acc  in
                          (env2, uu____6356))) (env1, []) binders1
             in
          (match uu____6229 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____6379 =
                 let check_what =
                   let uu____6405 = is_monadic rc_opt1  in
                   if uu____6405 then check_m else check_n  in
                 let uu____6419 = check_what env2 body1  in
                 match uu____6419 with
                 | (t,s_body,u_body) ->
                     let uu____6439 =
                       let uu____6442 =
                         let uu____6443 = is_monadic rc_opt1  in
                         if uu____6443 then M t else N t  in
                       comp_of_nm uu____6442  in
                     (uu____6439, s_body, u_body)
                  in
               (match uu____6379 with
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
                                 let uu____6480 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___338_6484  ->
                                           match uu___338_6484 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____6485 -> false))
                                    in
                                 if uu____6480
                                 then
                                   let uu____6486 =
                                     FStar_List.filter
                                       (fun uu___339_6490  ->
                                          match uu___339_6490 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____6491 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____6486
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____6500 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___340_6504  ->
                                         match uu___340_6504 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____6505 -> false))
                                  in
                               if uu____6500
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___341_6512  ->
                                        match uu___341_6512 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____6513 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____6514 =
                                   let uu____6515 =
                                     let uu____6520 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____6520
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____6515 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____6514
                               else
                                 (let uu____6526 =
                                    let uu___358_6527 = rc  in
                                    let uu____6528 =
                                      let uu____6533 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____6533
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___358_6527.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____6528;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___358_6527.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____6526))
                       in
                    let uu____6538 =
                      let comp1 =
                        let uu____6546 = is_monadic rc_opt1  in
                        let uu____6547 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____6546 uu____6547
                         in
                      let uu____6548 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____6548,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____6538 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____6586 =
                             let uu____6587 =
                               let uu____6604 =
                                 let uu____6607 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____6607 s_rc_opt  in
                               (s_binders1, s_body1, uu____6604)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6587  in
                           mk1 uu____6586  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____6625 =
                             let uu____6626 =
                               let uu____6643 =
                                 let uu____6646 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____6646 u_rc_opt  in
                               (u_binders2, u_body2, uu____6643)  in
                             FStar_Syntax_Syntax.Tm_abs uu____6626  in
                           mk1 uu____6625  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____6660;_};
            FStar_Syntax_Syntax.fv_delta = uu____6661;
            FStar_Syntax_Syntax.fv_qual = uu____6662;_}
          ->
          let uu____6665 =
            let uu____6670 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6670  in
          (match uu____6665 with
           | (uu____6701,t) ->
               let uu____6703 =
                 let uu____6704 = normalize1 t  in N uu____6704  in
               (uu____6703, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6705;
             FStar_Syntax_Syntax.vars = uu____6706;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6769 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6769 with
           | (unary_op,uu____6791) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6850;
             FStar_Syntax_Syntax.vars = uu____6851;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6927 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6927 with
           | (unary_op,uu____6949) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7014;
             FStar_Syntax_Syntax.vars = uu____7015;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____7045 = infer env a  in
          (match uu____7045 with
           | (t,s,u) ->
               let uu____7061 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7061 with
                | (head1,uu____7083) ->
                    let uu____7104 =
                      let uu____7105 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____7105  in
                    let uu____7106 =
                      let uu____7107 =
                        let uu____7108 =
                          let uu____7123 =
                            let uu____7132 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7132]  in
                          (head1, uu____7123)  in
                        FStar_Syntax_Syntax.Tm_app uu____7108  in
                      mk1 uu____7107  in
                    let uu____7161 =
                      let uu____7162 =
                        let uu____7163 =
                          let uu____7178 =
                            let uu____7187 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7187]  in
                          (head1, uu____7178)  in
                        FStar_Syntax_Syntax.Tm_app uu____7163  in
                      mk1 uu____7162  in
                    (uu____7104, uu____7106, uu____7161)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____7216;
             FStar_Syntax_Syntax.vars = uu____7217;_},(a1,uu____7219)::a2::[])
          ->
          let uu____7261 = infer env a1  in
          (match uu____7261 with
           | (t,s,u) ->
               let uu____7277 = FStar_Syntax_Util.head_and_args e  in
               (match uu____7277 with
                | (head1,uu____7299) ->
                    let uu____7320 =
                      let uu____7321 =
                        let uu____7322 =
                          let uu____7337 =
                            let uu____7346 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____7346; a2]  in
                          (head1, uu____7337)  in
                        FStar_Syntax_Syntax.Tm_app uu____7322  in
                      mk1 uu____7321  in
                    let uu____7381 =
                      let uu____7382 =
                        let uu____7383 =
                          let uu____7398 =
                            let uu____7407 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____7407; a2]  in
                          (head1, uu____7398)  in
                        FStar_Syntax_Syntax.Tm_app uu____7383  in
                      mk1 uu____7382  in
                    (t, uu____7320, uu____7381)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____7442;
             FStar_Syntax_Syntax.vars = uu____7443;_},uu____7444)
          ->
          let uu____7465 =
            let uu____7470 =
              let uu____7471 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____7471
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____7470)  in
          FStar_Errors.raise_error uu____7465 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
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
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____7536 = check_n env head1  in
          (match uu____7536 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____7558 =
                   let uu____7559 = FStar_Syntax_Subst.compress t  in
                   uu____7559.FStar_Syntax_Syntax.n  in
                 match uu____7558 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____7562 -> true
                 | uu____7575 -> false  in
               let rec flatten1 t =
                 let uu____7594 =
                   let uu____7595 = FStar_Syntax_Subst.compress t  in
                   uu____7595.FStar_Syntax_Syntax.n  in
                 match uu____7594 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____7612);
                                FStar_Syntax_Syntax.pos = uu____7613;
                                FStar_Syntax_Syntax.vars = uu____7614;_})
                     when is_arrow t1 ->
                     let uu____7639 = flatten1 t1  in
                     (match uu____7639 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7721,uu____7722)
                     -> flatten1 e1
                 | uu____7763 ->
                     let uu____7764 =
                       let uu____7769 =
                         let uu____7770 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____7770
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____7769)  in
                     FStar_Errors.raise_err uu____7764
                  in
               let uu____7783 = flatten1 t_head  in
               (match uu____7783 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____7843 =
                          let uu____7848 =
                            let uu____7849 = FStar_Util.string_of_int n1  in
                            let uu____7856 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____7867 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____7849 uu____7856 uu____7867
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____7848)
                           in
                        FStar_Errors.raise_err uu____7843)
                     else ();
                     (let uu____7875 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____7875 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____7924 args1 =
                            match uu____7924 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____8004 =
                                       let uu____8005 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____8005.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____8004
                                 | (binders3,[]) ->
                                     let uu____8035 =
                                       let uu____8036 =
                                         let uu____8039 =
                                           let uu____8040 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____8040
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____8039
                                          in
                                       uu____8036.FStar_Syntax_Syntax.n  in
                                     (match uu____8035 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____8067 =
                                            let uu____8068 =
                                              let uu____8069 =
                                                let uu____8082 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____8082)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____8069
                                               in
                                            mk1 uu____8068  in
                                          N uu____8067
                                      | uu____8093 -> failwith "wat?")
                                 | ([],uu____8094::uu____8095) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____8135)::binders3,(arg,uu____8138)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____8201 = FStar_List.splitAt n' binders1  in
                          (match uu____8201 with
                           | (binders2,uu____8233) ->
                               let uu____8258 =
                                 let uu____8277 =
                                   FStar_List.map2
                                     (fun uu____8327  ->
                                        fun uu____8328  ->
                                          match (uu____8327, uu____8328) with
                                          | ((bv,uu____8364),(arg,q)) ->
                                              let uu____8381 =
                                                let uu____8382 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____8382.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____8381 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____8399 ->
                                                   let uu____8400 =
                                                     let uu____8405 =
                                                       star_type' env arg  in
                                                     (uu____8405, q)  in
                                                   (uu____8400, [(arg, q)])
                                               | uu____8430 ->
                                                   let uu____8431 =
                                                     check_n env arg  in
                                                   (match uu____8431 with
                                                    | (uu____8452,s_arg,u_arg)
                                                        ->
                                                        let uu____8455 =
                                                          let uu____8462 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____8462
                                                          then
                                                            let uu____8469 =
                                                              let uu____8474
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____8474, q)
                                                               in
                                                            [uu____8469;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____8455))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____8277  in
                               (match uu____8258 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____8563 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____8574 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____8563, uu____8574)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____8638) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____8644) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____8650,uu____8651) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____8693 = let uu____8694 = env.tc_const c  in N uu____8694
             in
          (uu____8693, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____8701 ->
          let uu____8714 =
            let uu____8715 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____8715  in
          failwith uu____8714
      | FStar_Syntax_Syntax.Tm_type uu____8722 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____8729 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____8748 ->
          let uu____8755 =
            let uu____8756 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____8756  in
          failwith uu____8755
      | FStar_Syntax_Syntax.Tm_uvar uu____8763 ->
          let uu____8776 =
            let uu____8777 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____8777  in
          failwith uu____8776
      | FStar_Syntax_Syntax.Tm_delayed uu____8784 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____8813 =
            let uu____8814 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8814  in
          failwith uu____8813

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
          let uu____8861 = check_n env e0  in
          match uu____8861 with
          | (uu____8874,s_e0,u_e0) ->
              let uu____8877 =
                let uu____8906 =
                  FStar_List.map
                    (fun b  ->
                       let uu____8967 = FStar_Syntax_Subst.open_branch b  in
                       match uu____8967 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___359_9009 = env  in
                             let uu____9010 =
                               let uu____9011 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____9011
                                in
                             {
                               env = uu____9010;
                               subst = (uu___359_9009.subst);
                               tc_const = (uu___359_9009.tc_const)
                             }  in
                           let uu____9014 = f env1 body  in
                           (match uu____9014 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____9086 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____8906  in
              (match uu____8877 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____9190 = FStar_List.hd nms  in
                     match uu____9190 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___342_9198  ->
                          match uu___342_9198 with
                          | M uu____9199 -> true
                          | uu____9200 -> false) nms
                      in
                   let uu____9201 =
                     let uu____9238 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____9328  ->
                              match uu____9328 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____9505 =
                                         check env original_body (M t2)  in
                                       (match uu____9505 with
                                        | (uu____9542,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____9581,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____9238  in
                   (match uu____9201 with
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
                              (fun uu____9765  ->
                                 match uu____9765 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____9816 =
                                         let uu____9817 =
                                           let uu____9832 =
                                             let uu____9841 =
                                               let uu____9848 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____9851 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____9848, uu____9851)  in
                                             [uu____9841]  in
                                           (s_body, uu____9832)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____9817
                                          in
                                       mk1 uu____9816  in
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
                            let uu____9975 =
                              let uu____9976 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9976]  in
                            let uu____9989 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____9975 uu____9989
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____10013 =
                              let uu____10020 =
                                let uu____10025 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____10025
                                 in
                              [uu____10020]  in
                            let uu____10038 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____10013 uu____10038
                             in
                          let uu____10041 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____10080 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____10041, uu____10080)
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
                           let uu____10189 =
                             let uu____10190 =
                               let uu____10191 =
                                 let uu____10218 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____10218,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10191
                                in
                             mk1 uu____10190  in
                           let uu____10277 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____10189, uu____10277))))

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
              let uu____10340 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10340]  in
            let uu____10353 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____10353 with
            | (x_binders1,e21) ->
                let uu____10366 = infer env e1  in
                (match uu____10366 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____10383 = is_C t1  in
                       if uu____10383
                       then
                         let uu___360_10384 = binding  in
                         let uu____10385 =
                           let uu____10388 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____10388  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___360_10384.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___360_10384.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____10385;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___360_10384.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___360_10384.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___360_10384.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___360_10384.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___361_10391 = env  in
                       let uu____10392 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___362_10394 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___362_10394.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___362_10394.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10392;
                         subst = (uu___361_10391.subst);
                         tc_const = (uu___361_10391.tc_const)
                       }  in
                     let uu____10395 = proceed env1 e21  in
                     (match uu____10395 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___363_10412 = binding  in
                            let uu____10413 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___363_10412.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___363_10412.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____10413;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___363_10412.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___363_10412.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___363_10412.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___363_10412.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____10416 =
                            let uu____10417 =
                              let uu____10418 =
                                let uu____10431 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___364_10445 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___364_10445.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___364_10445.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___364_10445.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___364_10445.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___364_10445.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___364_10445.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10431)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10418  in
                            mk1 uu____10417  in
                          let uu____10446 =
                            let uu____10447 =
                              let uu____10448 =
                                let uu____10461 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___365_10475 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___365_10475.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___365_10475.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___365_10475.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___365_10475.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___365_10475.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___365_10475.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10461)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10448  in
                            mk1 uu____10447  in
                          (nm_rec, uu____10416, uu____10446))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___366_10480 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___366_10480.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___366_10480.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___366_10480.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___366_10480.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___366_10480.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___367_10482 = env  in
                       let uu____10483 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___368_10485 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___368_10485.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___368_10485.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____10483;
                         subst = (uu___367_10482.subst);
                         tc_const = (uu___367_10482.tc_const)
                       }  in
                     let uu____10486 = ensure_m env1 e21  in
                     (match uu____10486 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____10509 =
                              let uu____10510 =
                                let uu____10525 =
                                  let uu____10534 =
                                    let uu____10541 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____10544 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____10541, uu____10544)  in
                                  [uu____10534]  in
                                (s_e2, uu____10525)  in
                              FStar_Syntax_Syntax.Tm_app uu____10510  in
                            mk1 uu____10509  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____10575 =
                              let uu____10576 =
                                let uu____10591 =
                                  let uu____10600 =
                                    let uu____10607 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____10607)  in
                                  [uu____10600]  in
                                (s_e1, uu____10591)  in
                              FStar_Syntax_Syntax.Tm_app uu____10576  in
                            mk1 uu____10575  in
                          let uu____10632 =
                            let uu____10633 =
                              let uu____10634 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____10634]  in
                            FStar_Syntax_Util.abs uu____10633 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____10647 =
                            let uu____10648 =
                              let uu____10649 =
                                let uu____10662 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___369_10676 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___369_10676.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___369_10676.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___369_10676.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___369_10676.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___369_10676.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___369_10676.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____10662)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____10649  in
                            mk1 uu____10648  in
                          ((M t2), uu____10632, uu____10647)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10686 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____10686  in
      let uu____10687 = check env e mn  in
      match uu____10687 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10703 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10725 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____10725  in
      let uu____10726 = check env e mn  in
      match uu____10726 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10742 -> failwith "[check_m]: impossible"

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
        (let uu____10772 =
           let uu____10773 = is_C c  in Prims.op_Negation uu____10773  in
         if uu____10772 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____10783 =
           let uu____10784 = FStar_Syntax_Subst.compress c  in
           uu____10784.FStar_Syntax_Syntax.n  in
         match uu____10783 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____10809 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____10809 with
              | (wp_head,wp_args) ->
                  ((let uu____10847 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____10861 =
                           let uu____10862 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____10862
                            in
                         Prims.op_Negation uu____10861)
                       in
                    if uu____10847 then failwith "mismatch" else ());
                   (let uu____10870 =
                      let uu____10871 =
                        let uu____10886 =
                          FStar_List.map2
                            (fun uu____10916  ->
                               fun uu____10917  ->
                                 match (uu____10916, uu____10917) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____10956 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____10956
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____10959 =
                                           let uu____10964 =
                                             let uu____10965 =
                                               print_implicit q  in
                                             let uu____10966 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____10965 uu____10966
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____10964)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____10959)
                                      else ();
                                      (let uu____10968 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____10968, q)))) args wp_args
                           in
                        (head1, uu____10886)  in
                      FStar_Syntax_Syntax.Tm_app uu____10871  in
                    mk1 uu____10870)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____11004 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____11004 with
              | (binders_orig,comp1) ->
                  let uu____11011 =
                    let uu____11026 =
                      FStar_List.map
                        (fun uu____11060  ->
                           match uu____11060 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____11080 = is_C h  in
                               if uu____11080
                               then
                                 let w' =
                                   let uu____11092 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____11092
                                    in
                                 let uu____11093 =
                                   let uu____11100 =
                                     let uu____11107 =
                                       let uu____11112 =
                                         let uu____11113 =
                                           let uu____11114 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____11114  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____11113
                                          in
                                       (uu____11112, q)  in
                                     [uu____11107]  in
                                   (w', q) :: uu____11100  in
                                 (w', uu____11093)
                               else
                                 (let x =
                                    let uu____11135 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____11135
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____11026  in
                  (match uu____11011 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____11190 =
                           let uu____11193 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____11193
                            in
                         FStar_Syntax_Subst.subst_comp uu____11190 comp1  in
                       let app =
                         let uu____11197 =
                           let uu____11198 =
                             let uu____11213 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____11230 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____11231 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____11230, uu____11231)) bvs
                                in
                             (wp, uu____11213)  in
                           FStar_Syntax_Syntax.Tm_app uu____11198  in
                         mk1 uu____11197  in
                       let comp3 =
                         let uu____11243 = type_of_comp comp2  in
                         let uu____11244 = is_monadic_comp comp2  in
                         trans_G env uu____11243 uu____11244 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____11246,uu____11247) ->
             trans_F_ env e wp
         | uu____11288 -> failwith "impossible trans_F_")

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
            let uu____11293 =
              let uu____11294 = star_type' env h  in
              let uu____11297 =
                let uu____11306 =
                  let uu____11313 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____11313)  in
                [uu____11306]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____11294;
                FStar_Syntax_Syntax.effect_args = uu____11297;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____11293
          else
            (let uu____11329 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____11329)

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
    fun t  -> let uu____11348 = n env.env t  in star_type' env uu____11348
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____11367 = n env.env t  in check_n env uu____11367
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____11383 = n env.env c  in
        let uu____11384 = n env.env wp  in
        trans_F_ env uu____11383 uu____11384
  