open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }[@@deriving show]
let (__proj__Mkenv__item__env : env -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env -> fun tc_const -> { env; subst = []; tc_const }
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts, FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun binders ->
      fun a ->
        fun wp_a ->
          fun ed ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.EraseUniverses] env wp_a in
            let a1 =
              let uu___80_123 = a in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___80_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___80_123.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____124
              } in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s in
            (let uu____134 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____134
             then
               (d "Elaborating extra WP combinators";
                (let uu____136 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____136))
             else ());
            (let rec collect_binders t =
               let uu____150 =
                 let uu____151 =
                   let uu____154 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____154 in
                 uu____151.FStar_Syntax_Syntax.n in
               match uu____150 with
               | FStar_Syntax_Syntax.Tm_arrow (bs, comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1, uu____185) -> t1
                     | uu____194 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____197 = collect_binders rest in
                   FStar_List.append bs uu____197
               | FStar_Syntax_Syntax.Tm_type uu____208 -> []
               | uu____213 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____233 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____233 FStar_Syntax_Util.name_binders in
             (let uu____253 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____253
              then
                let uu____254 =
                  let uu____255 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____255 in
                d uu____254
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____289 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____289 with
                | (sigelt, fv) ->
                    ((let uu____297 =
                        let uu____300 = FStar_ST.op_Bang sigelts in sigelt ::
                          uu____300 in
                      FStar_ST.op_Colon_Equals sigelts uu____297);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____538 ->
                     match uu____538 with
                     | (t, b) ->
                         let uu____549 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____549)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t ->
                     let uu____582 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____582)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv ->
                     let uu____607 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____607) in
              let uu____608 =
                let uu____625 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____649 =
                        let uu____652 = FStar_Syntax_Syntax.bv_to_name t in
                        f uu____652 in
                      FStar_Syntax_Util.arrow gamma uu____649 in
                    let uu____653 =
                      let uu____654 =
                        let uu____661 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____662 =
                          let uu____665 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____665] in
                        uu____661 :: uu____662 in
                      FStar_List.append binders uu____654 in
                    FStar_Syntax_Util.abs uu____653 body
                      FStar_Pervasives_Native.None in
                  let uu____670 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____671 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____670, uu____671) in
                match uu____625 with
                | (ctx_def, gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____711 =
                        let uu____712 =
                          let uu____727 =
                            let uu____734 =
                              FStar_List.map
                                (fun uu____754 ->
                                   match uu____754 with
                                   | (bv, uu____764) ->
                                       let uu____765 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____766 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____765, uu____766)) binders in
                            let uu____767 =
                              let uu____774 =
                                let uu____779 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____780 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____779, uu____780) in
                              let uu____781 =
                                let uu____788 =
                                  let uu____793 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____793) in
                                [uu____788] in
                              uu____774 :: uu____781 in
                            FStar_List.append uu____734 uu____767 in
                          (fv, uu____727) in
                        FStar_Syntax_Syntax.Tm_app uu____712 in
                      mk1 uu____711 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____608 with
              | (env1, mk_ctx, mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____858 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____858 in
                    let ret1 =
                      let uu____862 =
                        let uu____863 =
                          let uu____866 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____866 in
                        FStar_Syntax_Util.residual_tot uu____863 in
                      FStar_Pervasives_Native.Some uu____862 in
                    let body =
                      let uu____868 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____868 ret1 in
                    let uu____869 =
                      let uu____870 = mk_all_implicit binders in
                      let uu____877 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____870 uu____877 in
                    FStar_Syntax_Util.abs uu____869 body ret1 in
                  let c_pure1 =
                    let uu____905 = mk_lid "pure" in
                    register env1 uu____905 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____910 =
                        let uu____911 =
                          let uu____912 =
                            let uu____919 =
                              let uu____920 =
                                let uu____921 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____921 in
                              FStar_Syntax_Syntax.mk_binder uu____920 in
                            [uu____919] in
                          let uu____922 =
                            let uu____925 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____925 in
                          FStar_Syntax_Util.arrow uu____912 uu____922 in
                        mk_gctx uu____911 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____910 in
                    let r =
                      let uu____927 =
                        let uu____928 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____928 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____927 in
                    let ret1 =
                      let uu____932 =
                        let uu____933 =
                          let uu____936 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____936 in
                        FStar_Syntax_Util.residual_tot uu____933 in
                      FStar_Pervasives_Native.Some uu____932 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____944 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____947 =
                          let uu____956 =
                            let uu____959 =
                              let uu____960 =
                                let uu____961 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____961
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____960 in
                            [uu____959] in
                          FStar_List.append gamma_as_args uu____956 in
                        FStar_Syntax_Util.mk_app uu____944 uu____947 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____964 =
                      let uu____965 = mk_all_implicit binders in
                      let uu____972 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____965 uu____972 in
                    FStar_Syntax_Util.abs uu____964 outer_body ret1 in
                  let c_app1 =
                    let uu____1008 = mk_lid "app" in
                    register env1 uu____1008 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1015 =
                        let uu____1022 =
                          let uu____1023 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1023 in
                        [uu____1022] in
                      let uu____1024 =
                        let uu____1027 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1027 in
                      FStar_Syntax_Util.arrow uu____1015 uu____1024 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1030 =
                        let uu____1031 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1031 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1030 in
                    let ret1 =
                      let uu____1035 =
                        let uu____1036 =
                          let uu____1039 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1039 in
                        FStar_Syntax_Util.residual_tot uu____1036 in
                      FStar_Pervasives_Native.Some uu____1035 in
                    let uu____1040 =
                      let uu____1041 = mk_all_implicit binders in
                      let uu____1048 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____1041 uu____1048 in
                    let uu____1083 =
                      let uu____1084 =
                        let uu____1093 =
                          let uu____1096 =
                            let uu____1099 =
                              let uu____1108 =
                                let uu____1111 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____1111] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1108 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1099 in
                          let uu____1112 =
                            let uu____1117 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____1117] in
                          uu____1096 :: uu____1112 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1093 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1084 in
                    FStar_Syntax_Util.abs uu____1040 uu____1083 ret1 in
                  let c_lift11 =
                    let uu____1121 = mk_lid "lift1" in
                    register env1 uu____1121 c_lift1 in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1129 =
                        let uu____1136 =
                          let uu____1137 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1137 in
                        let uu____1138 =
                          let uu____1141 =
                            let uu____1142 =
                              FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____1142 in
                          [uu____1141] in
                        uu____1136 :: uu____1138 in
                      let uu____1143 =
                        let uu____1146 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1146 in
                      FStar_Syntax_Util.arrow uu____1129 uu____1143 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1149 =
                        let uu____1150 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1150 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1149 in
                    let a2 =
                      let uu____1152 =
                        let uu____1153 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____1153 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1152 in
                    let ret1 =
                      let uu____1157 =
                        let uu____1158 =
                          let uu____1161 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____1161 in
                        FStar_Syntax_Util.residual_tot uu____1158 in
                      FStar_Pervasives_Native.Some uu____1157 in
                    let uu____1162 =
                      let uu____1163 = mk_all_implicit binders in
                      let uu____1170 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1163 uu____1170 in
                    let uu____1213 =
                      let uu____1214 =
                        let uu____1223 =
                          let uu____1226 =
                            let uu____1229 =
                              let uu____1238 =
                                let uu____1241 =
                                  let uu____1244 =
                                    let uu____1253 =
                                      let uu____1256 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1256] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1253 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1244 in
                                let uu____1257 =
                                  let uu____1262 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1262] in
                                uu____1241 :: uu____1257 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1238 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1229 in
                          let uu____1265 =
                            let uu____1270 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1270] in
                          uu____1226 :: uu____1265 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1223 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1214 in
                    FStar_Syntax_Util.abs uu____1162 uu____1213 ret1 in
                  let c_lift21 =
                    let uu____1274 = mk_lid "lift2" in
                    register env1 uu____1274 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1281 =
                        let uu____1288 =
                          let uu____1289 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1289 in
                        [uu____1288] in
                      let uu____1290 =
                        let uu____1293 =
                          let uu____1294 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1294 in
                        FStar_Syntax_Syntax.mk_Total uu____1293 in
                      FStar_Syntax_Util.arrow uu____1281 uu____1290 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1299 =
                        let uu____1300 =
                          let uu____1303 =
                            let uu____1304 =
                              let uu____1311 =
                                let uu____1312 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1312 in
                              [uu____1311] in
                            let uu____1313 =
                              let uu____1316 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1316 in
                            FStar_Syntax_Util.arrow uu____1304 uu____1313 in
                          mk_ctx uu____1303 in
                        FStar_Syntax_Util.residual_tot uu____1300 in
                      FStar_Pervasives_Native.Some uu____1299 in
                    let e1 =
                      let uu____1318 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1318 in
                    let body =
                      let uu____1320 =
                        let uu____1321 =
                          let uu____1328 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1328] in
                        FStar_List.append gamma uu____1321 in
                      let uu____1333 =
                        let uu____1334 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1337 =
                          let uu____1346 =
                            let uu____1347 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1347 in
                          let uu____1348 = args_of_binders1 gamma in
                          uu____1346 :: uu____1348 in
                        FStar_Syntax_Util.mk_app uu____1334 uu____1337 in
                      FStar_Syntax_Util.abs uu____1320 uu____1333 ret1 in
                    let uu____1351 =
                      let uu____1352 = mk_all_implicit binders in
                      let uu____1359 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1352 uu____1359 in
                    FStar_Syntax_Util.abs uu____1351 body ret1 in
                  let c_push1 =
                    let uu____1391 = mk_lid "push" in
                    register env1 uu____1391 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1413 =
                        let uu____1414 =
                          let uu____1429 = args_of_binders1 binders in
                          (c, uu____1429) in
                        FStar_Syntax_Syntax.Tm_app uu____1414 in
                      mk1 uu____1413
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1439 =
                        let uu____1440 =
                          let uu____1447 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1448 =
                            let uu____1451 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1451] in
                          uu____1447 :: uu____1448 in
                        let uu____1452 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1440 uu____1452 in
                      FStar_Syntax_Syntax.mk_Total uu____1439 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.kprop in
                    let uu____1456 =
                      let uu____1457 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1457 in
                    let uu____1468 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1470 =
                        let uu____1473 =
                          let uu____1482 =
                            let uu____1485 =
                              let uu____1488 =
                                let uu____1497 =
                                  let uu____1498 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1498 in
                                [uu____1497] in
                              FStar_Syntax_Util.mk_app l_ite uu____1488 in
                            [uu____1485] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1482 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1473 in
                      FStar_Syntax_Util.ascribe uu____1470
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1456 uu____1468
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1518 = mk_lid "wp_if_then_else" in
                    register env1 uu____1518 wp_if_then_else in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1 in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.kprop in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None in
                    let body =
                      let uu____1529 =
                        let uu____1538 =
                          let uu____1541 =
                            let uu____1544 =
                              let uu____1553 =
                                let uu____1556 =
                                  let uu____1559 =
                                    let uu____1568 =
                                      let uu____1569 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1569 in
                                    [uu____1568] in
                                  FStar_Syntax_Util.mk_app l_and uu____1559 in
                                [uu____1556] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1553 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1544 in
                          let uu____1574 =
                            let uu____1579 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1579] in
                          uu____1541 :: uu____1574 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1538 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1529 in
                    let uu____1582 =
                      let uu____1583 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1583 in
                    FStar_Syntax_Util.abs uu____1582 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1595 = mk_lid "wp_assert" in
                    register env1 uu____1595 wp_assert in
                  let wp_assert2 = mk_generic_app wp_assert1 in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.kprop in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None in
                    let body =
                      let uu____1606 =
                        let uu____1615 =
                          let uu____1618 =
                            let uu____1621 =
                              let uu____1630 =
                                let uu____1633 =
                                  let uu____1636 =
                                    let uu____1645 =
                                      let uu____1646 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1646 in
                                    [uu____1645] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1636 in
                                [uu____1633] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1630 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1621 in
                          let uu____1651 =
                            let uu____1656 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1656] in
                          uu____1618 :: uu____1651 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1615 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1606 in
                    let uu____1659 =
                      let uu____1660 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1660 in
                    FStar_Syntax_Util.abs uu____1659 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1672 = mk_lid "wp_assume" in
                    register env1 uu____1672 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1681 =
                        let uu____1688 =
                          let uu____1689 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1689 in
                        [uu____1688] in
                      let uu____1690 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1681 uu____1690 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1697 =
                        let uu____1706 =
                          let uu____1709 =
                            let uu____1712 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1712 in
                          let uu____1721 =
                            let uu____1726 =
                              let uu____1729 =
                                let uu____1738 =
                                  let uu____1741 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1741] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1738 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1729 in
                            [uu____1726] in
                          uu____1709 :: uu____1721 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1706 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1697 in
                    let uu____1748 =
                      let uu____1749 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1749 in
                    FStar_Syntax_Util.abs uu____1748 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1761 = mk_lid "wp_close" in
                    register env1 uu____1761 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1771 =
                      let uu____1772 =
                        let uu____1773 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1773 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1772 in
                    FStar_Pervasives_Native.Some uu____1771 in
                  let mk_forall1 x body =
                    let uu____1789 =
                      let uu____1796 =
                        let uu____1797 =
                          let uu____1812 =
                            let uu____1815 =
                              let uu____1816 =
                                let uu____1817 =
                                  let uu____1818 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1818] in
                                FStar_Syntax_Util.abs uu____1817 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1816 in
                            [uu____1815] in
                          (FStar_Syntax_Util.tforall, uu____1812) in
                        FStar_Syntax_Syntax.Tm_app uu____1797 in
                      FStar_Syntax_Syntax.mk uu____1796 in
                    uu____1789 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1830 =
                      let uu____1831 = FStar_Syntax_Subst.compress t in
                      uu____1831.FStar_Syntax_Syntax.n in
                    match uu____1830 with
                    | FStar_Syntax_Syntax.Tm_type uu____1834 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu____1860 ->
                              match uu____1860 with
                              | (b, uu____1866) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1867 -> true in
                  let rec is_monotonic t =
                    let uu____1874 =
                      let uu____1875 = FStar_Syntax_Subst.compress t in
                      uu____1875.FStar_Syntax_Syntax.n in
                    match uu____1874 with
                    | FStar_Syntax_Syntax.Tm_type uu____1878 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu____1904 ->
                              match uu____1904 with
                              | (b, uu____1910) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1911 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1977 =
                      let uu____1978 = FStar_Syntax_Subst.compress t1 in
                      uu____1978.FStar_Syntax_Syntax.n in
                    match uu____1977 with
                    | FStar_Syntax_Syntax.Tm_type uu____1981 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                             (b, uu____1984);
                           FStar_Syntax_Syntax.pos = uu____1985;
                           FStar_Syntax_Syntax.vars = uu____1986;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2020 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2020
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2023 =
                              let uu____2026 =
                                let uu____2035 =
                                  let uu____2036 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2036 in
                                [uu____2035] in
                              FStar_Syntax_Util.mk_app x uu____2026 in
                            let uu____2037 =
                              let uu____2040 =
                                let uu____2049 =
                                  let uu____2050 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2050 in
                                [uu____2049] in
                              FStar_Syntax_Util.mk_app y uu____2040 in
                            mk_rel1 b uu____2023 uu____2037 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2055 =
                               let uu____2056 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2059 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2056 uu____2059 in
                             let uu____2062 =
                               let uu____2063 =
                                 let uu____2066 =
                                   let uu____2075 =
                                     let uu____2076 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2076 in
                                   [uu____2075] in
                                 FStar_Syntax_Util.mk_app x uu____2066 in
                               let uu____2077 =
                                 let uu____2080 =
                                   let uu____2089 =
                                     let uu____2090 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2090 in
                                   [uu____2089] in
                                 FStar_Syntax_Util.mk_app y uu____2080 in
                               mk_rel1 b uu____2063 uu____2077 in
                             FStar_Syntax_Util.mk_imp uu____2055 uu____2062 in
                           let uu____2091 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2091)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                             (b, uu____2094);
                           FStar_Syntax_Syntax.pos = uu____2095;
                           FStar_Syntax_Syntax.vars = uu____2096;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2130 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2130
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2133 =
                              let uu____2136 =
                                let uu____2145 =
                                  let uu____2146 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2146 in
                                [uu____2145] in
                              FStar_Syntax_Util.mk_app x uu____2136 in
                            let uu____2147 =
                              let uu____2150 =
                                let uu____2159 =
                                  let uu____2160 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2160 in
                                [uu____2159] in
                              FStar_Syntax_Util.mk_app y uu____2150 in
                            mk_rel1 b uu____2133 uu____2147 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2165 =
                               let uu____2166 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2169 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2166 uu____2169 in
                             let uu____2172 =
                               let uu____2173 =
                                 let uu____2176 =
                                   let uu____2185 =
                                     let uu____2186 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2186 in
                                   [uu____2185] in
                                 FStar_Syntax_Util.mk_app x uu____2176 in
                               let uu____2187 =
                                 let uu____2190 =
                                   let uu____2199 =
                                     let uu____2200 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2200 in
                                   [uu____2199] in
                                 FStar_Syntax_Util.mk_app y uu____2190 in
                               mk_rel1 b uu____2173 uu____2187 in
                             FStar_Syntax_Util.mk_imp uu____2165 uu____2172 in
                           let uu____2201 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2201)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1, comp)
                        ->
                        let t2 =
                          let uu___81_2232 = t1 in
                          let uu____2233 =
                            let uu____2234 =
                              let uu____2247 =
                                let uu____2248 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2248 in
                              ([binder], uu____2247) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2234 in
                          {
                            FStar_Syntax_Syntax.n = uu____2233;
                            FStar_Syntax_Syntax.pos =
                              (uu___81_2232.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___81_2232.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2263 ->
                        failwith "unhandled arrow"
                    | uu____2276 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1 in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1 in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] env1 t in
                      let uu____2297 =
                        let uu____2298 = FStar_Syntax_Subst.compress t1 in
                        uu____2298.FStar_Syntax_Syntax.n in
                      match uu____2297 with
                      | FStar_Syntax_Syntax.Tm_type uu____2301 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1, args) when
                          let uu____2324 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2324
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2343 =
                                let uu____2344 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2344 i in
                              FStar_Syntax_Syntax.fvar uu____2343
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2371 =
                            let uu____2378 =
                              FStar_List.mapi
                                (fun i ->
                                   fun uu____2392 ->
                                     match uu____2392 with
                                     | (t2, q) ->
                                         let uu____2399 = project i x in
                                         let uu____2400 = project i y in
                                         mk_stronger t2 uu____2399 uu____2400)
                                args in
                            match uu____2378 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2371 with
                           | (rel0, rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (b, uu____2427);
                             FStar_Syntax_Syntax.pos = uu____2428;
                             FStar_Syntax_Syntax.vars = uu____2429;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu____2467 ->
                                   match uu____2467 with
                                   | (bv, q) ->
                                       let uu____2474 =
                                         let uu____2475 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2475 in
                                       FStar_Syntax_Syntax.gen_bv uu____2474
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu____2482 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2482) bvs in
                          let body =
                            let uu____2484 = FStar_Syntax_Util.mk_app x args in
                            let uu____2485 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2484 uu____2485 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall1 bv body1) bvs
                            body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Total (b, uu____2492);
                             FStar_Syntax_Syntax.pos = uu____2493;
                             FStar_Syntax_Syntax.vars = uu____2494;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu____2532 ->
                                   match uu____2532 with
                                   | (bv, q) ->
                                       let uu____2539 =
                                         let uu____2540 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2540 in
                                       FStar_Syntax_Syntax.gen_bv uu____2539
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu____2547 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2547) bvs in
                          let body =
                            let uu____2549 = FStar_Syntax_Util.mk_app x args in
                            let uu____2550 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2549 uu____2550 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall1 bv body1) bvs
                            body
                      | uu____2555 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2557 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2558 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2559 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2557 uu____2558 uu____2559 in
                    let uu____2560 =
                      let uu____2561 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2561 in
                    FStar_Syntax_Util.abs uu____2560 body ret_tot_type in
                  let stronger1 =
                    let uu____2589 = mk_lid "stronger" in
                    register env1 uu____2589 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2595 = FStar_Util.prefix gamma in
                    match uu____2595 with
                    | (wp_args, post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2640 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2640 in
                          let uu____2643 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2643 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1, [], body))
                              ->
                              let k_app =
                                let uu____2653 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2653 in
                              let guard_free1 =
                                let uu____2663 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2663 in
                              let pat =
                                let uu____2667 =
                                  let uu____2676 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2676] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2667 in
                              let pattern_guarded_body =
                                let uu____2680 =
                                  let uu____2681 =
                                    let uu____2688 =
                                      let uu____2689 =
                                        let uu____2700 =
                                          let uu____2703 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2703] in
                                        [uu____2700] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2689 in
                                    (body, uu____2688) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2681 in
                                mk1 uu____2680 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2708 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2712 =
                            let uu____2713 =
                              let uu____2714 =
                                let uu____2715 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2718 =
                                  let uu____2727 = args_of_binders1 wp_args in
                                  let uu____2730 =
                                    let uu____2733 =
                                      let uu____2734 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2734 in
                                    [uu____2733] in
                                  FStar_List.append uu____2727 uu____2730 in
                                FStar_Syntax_Util.mk_app uu____2715
                                  uu____2718 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2714 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2713 in
                          FStar_Syntax_Util.abs gamma uu____2712
                            ret_gtot_type in
                        let uu____2735 =
                          let uu____2736 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2736 in
                        FStar_Syntax_Util.abs uu____2735 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2748 = mk_lid "wp_ite" in
                    register env1 uu____2748 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2754 = FStar_Util.prefix gamma in
                    match uu____2754 with
                    | (wp_args, post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2797 =
                            let uu____2798 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2801 =
                              let uu____2810 =
                                let uu____2811 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2811 in
                              [uu____2810] in
                            FStar_Syntax_Util.mk_app uu____2798 uu____2801 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2797 in
                        let uu____2812 =
                          let uu____2813 =
                            let uu____2820 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2820 gamma in
                          FStar_List.append binders uu____2813 in
                        FStar_Syntax_Util.abs uu____2812 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2836 = mk_lid "null_wp" in
                    register env1 uu____2836 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2845 =
                        let uu____2854 =
                          let uu____2857 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2858 =
                            let uu____2861 =
                              let uu____2864 =
                                let uu____2873 =
                                  let uu____2874 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2874 in
                                [uu____2873] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2864 in
                            let uu____2875 =
                              let uu____2880 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2880] in
                            uu____2861 :: uu____2875 in
                          uu____2857 :: uu____2858 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2854 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2845 in
                    let uu____2883 =
                      let uu____2884 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2884 in
                    FStar_Syntax_Util.abs uu____2883 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2896 = mk_lid "wp_trivial" in
                    register env1 uu____2896 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2901 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2901
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2908 =
                      let uu____2911 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____2911 in
                    let uu____3017 =
                      let uu___82_3018 = ed in
                      let uu____3019 =
                        let uu____3020 = c wp_if_then_else2 in
                        ([], uu____3020) in
                      let uu____3023 =
                        let uu____3024 = c wp_ite2 in ([], uu____3024) in
                      let uu____3027 =
                        let uu____3028 = c stronger2 in ([], uu____3028) in
                      let uu____3031 =
                        let uu____3032 = c wp_close2 in ([], uu____3032) in
                      let uu____3035 =
                        let uu____3036 = c wp_assert2 in ([], uu____3036) in
                      let uu____3039 =
                        let uu____3040 = c wp_assume2 in ([], uu____3040) in
                      let uu____3043 =
                        let uu____3044 = c null_wp2 in ([], uu____3044) in
                      let uu____3047 =
                        let uu____3048 = c wp_trivial2 in ([], uu____3048) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___82_3018.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___82_3018.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___82_3018.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___82_3018.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___82_3018.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___82_3018.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___82_3018.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3019;
                        FStar_Syntax_Syntax.ite_wp = uu____3023;
                        FStar_Syntax_Syntax.stronger = uu____3027;
                        FStar_Syntax_Syntax.close_wp = uu____3031;
                        FStar_Syntax_Syntax.assert_p = uu____3035;
                        FStar_Syntax_Syntax.assume_p = uu____3039;
                        FStar_Syntax_Syntax.null_wp = uu____3043;
                        FStar_Syntax_Syntax.trivial = uu____3047;
                        FStar_Syntax_Syntax.repr =
                          (uu___82_3018.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___82_3018.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___82_3018.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___82_3018.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___82_3018.FStar_Syntax_Syntax.eff_attrs)
                      } in
                    (uu____2908, uu____3017)))))
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env -> env.env
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env ->
    fun env' ->
      let uu___83_3068 = dmff_env in
      {
        env = env';
        subst = (uu___83_3068.subst);
        tc_const = (uu___83_3068.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee -> match projectee with | N _0 -> true | uu____3085 -> false
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | N _0 -> _0
let (uu___is_M : nm -> Prims.bool) =
  fun projectee -> match projectee with | M _0 -> true | uu____3099 -> false
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | M _0 -> _0
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___69_3111 ->
    match uu___69_3111 with
    | FStar_Syntax_Syntax.Total (t, uu____3113) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___68_3126 ->
                match uu___68_3126 with
                | FStar_Syntax_Syntax.CPS -> true
                | uu____3127 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____3129 =
          let uu____3130 =
            let uu____3131 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3131 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3130 in
        failwith uu____3129
    | FStar_Syntax_Syntax.GTotal uu____3132 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let (string_of_nm : nm -> Prims.string) =
  fun uu___70_3145 ->
    match uu___70_3145 with
    | N t ->
        let uu____3147 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____3147
    | M t ->
        let uu____3149 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____3149
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1 ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3155,
         { FStar_Syntax_Syntax.n = n2; FStar_Syntax_Syntax.pos = uu____3157;
           FStar_Syntax_Syntax.vars = uu____3158;_})
        -> nm_of_comp n2
    | uu____3175 -> failwith "unexpected_argument: [is_monadic_arrow]"
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    let uu____3185 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____3185 with | M uu____3186 -> true | N uu____3187 -> false
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Not_found -> true | uu____3193 -> false
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ ->
    let star_once typ1 =
      let uu____3207 =
        let uu____3214 =
          let uu____3215 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3215 in
        [uu____3214] in
      let uu____3216 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.kprop in
      FStar_Syntax_Util.arrow uu____3207 uu____3216 in
    let uu____3219 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____3219
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk1 ->
    fun env ->
      fun a ->
        let uu____3264 =
          let uu____3265 =
            let uu____3278 =
              let uu____3285 =
                let uu____3290 =
                  let uu____3291 = star_type' env a in
                  FStar_Syntax_Syntax.null_bv uu____3291 in
                let uu____3292 = FStar_Syntax_Syntax.as_implicit false in
                (uu____3290, uu____3292) in
              [uu____3285] in
            let uu____3301 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.kprop in
            (uu____3278, uu____3301) in
          FStar_Syntax_Syntax.Tm_arrow uu____3265 in
        mk1 uu____3264
and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk1 in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders, uu____3335) ->
          let binders1 =
            FStar_List.map
              (fun uu____3371 ->
                 match uu____3371 with
                 | (bv, aqual) ->
                     let uu____3382 =
                       let uu___84_3383 = bv in
                       let uu____3384 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___84_3383.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___84_3383.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3384
                       } in
                     (uu____3382, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3387,
                {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                    (hn, uu____3389);
                  FStar_Syntax_Syntax.pos = uu____3390;
                  FStar_Syntax_Syntax.vars = uu____3391;_})
               ->
               let uu____3416 =
                 let uu____3417 =
                   let uu____3430 =
                     let uu____3431 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3431 in
                   (binders1, uu____3430) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3417 in
               mk1 uu____3416
           | uu____3438 ->
               let uu____3439 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3439 with
                | N hn ->
                    let uu____3441 =
                      let uu____3442 =
                        let uu____3455 =
                          let uu____3456 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3456 in
                        (binders1, uu____3455) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3442 in
                    mk1 uu____3441
                | M a ->
                    let uu____3464 =
                      let uu____3465 =
                        let uu____3478 =
                          let uu____3485 =
                            let uu____3492 =
                              let uu____3497 =
                                let uu____3498 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3498 in
                              let uu____3499 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3497, uu____3499) in
                            [uu____3492] in
                          FStar_List.append binders1 uu____3485 in
                        let uu____3512 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.kprop in
                        (uu____3478, uu____3512) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3465 in
                    mk1 uu____3464))
      | FStar_Syntax_Syntax.Tm_app (head1, args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3590 = f x in
                    FStar_Util.string_builder_append strb uu____3590);
                   FStar_List.iter
                     (fun x1 ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3597 = f x1 in
                         FStar_Util.string_builder_append strb uu____3597))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3599 =
              let uu____3604 =
                let uu____3605 = FStar_Syntax_Print.term_to_string t2 in
                let uu____3606 =
                  string_of_set FStar_Syntax_Print.bv_to_string s in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3605 uu____3606 in
              (FStar_Errors.Warning_DependencyFound, uu____3604) in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3599 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3618 =
              let uu____3619 = FStar_Syntax_Subst.compress ty in
              uu____3619.FStar_Syntax_Syntax.n in
            match uu____3618 with
            | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
                let uu____3640 =
                  let uu____3641 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3641 in
                if uu____3640
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3671 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3671 s in
                       let uu____3674 =
                         let uu____3675 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3675 in
                       if uu____3674
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else () in
                     let uu____3678 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3678 with
                     | (binders1, c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s ->
                                fun uu____3700 ->
                                  match uu____3700 with
                                  | (bv, uu____3710) ->
                                      (non_dependent_or_raise s
                                         bv.FStar_Syntax_Syntax.sort;
                                       FStar_Util.set_add bv s))
                             FStar_Syntax_Syntax.no_names binders1 in
                         let ct = FStar_Syntax_Util.comp_result c1 in
                         (non_dependent_or_raise s ct;
                          (let k = n1 - (FStar_List.length binders1) in
                           if k > (Prims.parse_int "0")
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found -> false)
            | uu____3724 ->
                ((let uu____3726 =
                    let uu____3731 =
                      let uu____3732 = FStar_Syntax_Print.term_to_string ty in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3732 in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3731) in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3726);
                 false) in
          let rec is_valid_application head2 =
            let uu____3739 =
              let uu____3740 = FStar_Syntax_Subst.compress head2 in
              uu____3740.FStar_Syntax_Syntax.n in
            match uu____3739 with
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
                  (let uu____3745 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3745)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3747 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3747 with
                 | ((uu____3756, ty), uu____3758) ->
                     let uu____3763 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3763
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       let uu____3771 =
                         let uu____3772 = FStar_Syntax_Subst.compress res in
                         uu____3772.FStar_Syntax_Syntax.n in
                       (match uu____3771 with
                        | FStar_Syntax_Syntax.Tm_app uu____3775 -> true
                        | uu____3790 ->
                            ((let uu____3792 =
                                let uu____3797 =
                                  let uu____3798 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3798 in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3797) in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3792);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3800 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3801 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2, uu____3803) ->
                is_valid_application t2
            | uu____3808 -> false in
          let uu____3809 = is_valid_application head1 in
          if uu____3809
          then
            let uu____3810 =
              let uu____3811 =
                let uu____3826 =
                  FStar_List.map
                    (fun uu____3847 ->
                       match uu____3847 with
                       | (t2, qual) ->
                           let uu____3864 = star_type' env t2 in
                           (uu____3864, qual)) args in
                (head1, uu____3826) in
              FStar_Syntax_Syntax.Tm_app uu____3811 in
            mk1 uu____3810
          else
            (let uu____3874 =
               let uu____3879 =
                 let uu____3880 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3880 in
               (FStar_Errors.Fatal_WrongTerm, uu____3879) in
             FStar_Errors.raise_err uu____3874)
      | FStar_Syntax_Syntax.Tm_bvar uu____3881 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3882 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3883 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3884 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders, repr, something) ->
          let uu____3908 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3908 with
           | (binders1, repr1) ->
               let env1 =
                 let uu___87_3916 = env in
                 let uu____3917 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3917;
                   subst = (uu___87_3916.subst);
                   tc_const = (uu___87_3916.tc_const)
                 } in
               let repr2 = star_type' env1 repr1 in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x, t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)] in
          let t3 = FStar_Syntax_Subst.subst subst1 t2 in
          let t4 = star_type' env t3 in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))] in
          let t5 = FStar_Syntax_Subst.subst subst2 t4 in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___88_3937 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___88_3937.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___88_3937.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2, m) ->
          let uu____3944 =
            let uu____3945 =
              let uu____3952 = star_type' env t2 in (uu____3952, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3945 in
          mk1 uu____3944
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Util.Inl t2, FStar_Pervasives_Native.None), something)
          ->
          let uu____4000 =
            let uu____4001 =
              let uu____4028 = star_type' env e in
              let uu____4029 =
                let uu____4044 =
                  let uu____4051 = star_type' env t2 in
                  FStar_Util.Inl uu____4051 in
                (uu____4044, FStar_Pervasives_Native.None) in
              (uu____4028, uu____4029, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____4001 in
          mk1 uu____4000
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Util.Inr c, FStar_Pervasives_Native.None), something) ->
          let uu____4129 =
            let uu____4130 =
              let uu____4157 = star_type' env e in
              let uu____4158 =
                let uu____4173 =
                  let uu____4180 =
                    star_type' env (FStar_Syntax_Util.comp_result c) in
                  FStar_Util.Inl uu____4180 in
                (uu____4173, FStar_Pervasives_Native.None) in
              (uu____4157, uu____4158, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____4130 in
          mk1 uu____4129
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4211, (uu____4212, FStar_Pervasives_Native.Some uu____4213),
           uu____4214)
          ->
          let uu____4263 =
            let uu____4268 =
              let uu____4269 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4269 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4268) in
          FStar_Errors.raise_err uu____4263
      | FStar_Syntax_Syntax.Tm_refine uu____4270 ->
          let uu____4277 =
            let uu____4282 =
              let uu____4283 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4283 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4282) in
          FStar_Errors.raise_err uu____4277
      | FStar_Syntax_Syntax.Tm_uinst uu____4284 ->
          let uu____4291 =
            let uu____4296 =
              let uu____4297 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4297 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4296) in
          FStar_Errors.raise_err uu____4291
      | FStar_Syntax_Syntax.Tm_quoted uu____4298 ->
          let uu____4305 =
            let uu____4310 =
              let uu____4311 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4311 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4310) in
          FStar_Errors.raise_err uu____4305
      | FStar_Syntax_Syntax.Tm_constant uu____4312 ->
          let uu____4313 =
            let uu____4318 =
              let uu____4319 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4319 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4318) in
          FStar_Errors.raise_err uu____4313
      | FStar_Syntax_Syntax.Tm_match uu____4320 ->
          let uu____4343 =
            let uu____4348 =
              let uu____4349 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4349 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4348) in
          FStar_Errors.raise_err uu____4343
      | FStar_Syntax_Syntax.Tm_let uu____4350 ->
          let uu____4363 =
            let uu____4368 =
              let uu____4369 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4369 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4368) in
          FStar_Errors.raise_err uu____4363
      | FStar_Syntax_Syntax.Tm_uvar uu____4370 ->
          let uu____4387 =
            let uu____4392 =
              let uu____4393 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4393 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4392) in
          FStar_Errors.raise_err uu____4387
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____4394 =
            let uu____4399 =
              let uu____4400 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4400 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4399) in
          FStar_Errors.raise_err uu____4394
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4402 = FStar_Syntax_Util.unfold_lazy i in
          star_type' env uu____4402
      | FStar_Syntax_Syntax.Tm_delayed uu____4405 -> failwith "impossible"
let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___72_4436 ->
    match uu___72_4436 with
    | FStar_Pervasives_Native.None -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___71_4443 ->
                match uu___71_4443 with
                | FStar_Syntax_Syntax.CPS -> true
                | uu____4444 -> false))
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    let uu____4450 =
      let uu____4451 = FStar_Syntax_Subst.compress t in
      uu____4451.FStar_Syntax_Syntax.n in
    match uu____4450 with
    | FStar_Syntax_Syntax.Tm_app (head1, args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4477 =
            let uu____4478 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____4478 in
          is_C uu____4477 in
        if r
        then
          ((let uu____4494 =
              let uu____4495 =
                FStar_List.for_all
                  (fun uu____4503 ->
                     match uu____4503 with | (h, uu____4509) -> is_C h) args in
              Prims.op_Negation uu____4495 in
            if uu____4494 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4513 =
              let uu____4514 =
                FStar_List.for_all
                  (fun uu____4523 ->
                     match uu____4523 with
                     | (h, uu____4529) ->
                         let uu____4530 = is_C h in
                         Prims.op_Negation uu____4530) args in
              Prims.op_Negation uu____4514 in
            if uu____4513 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
        let uu____4550 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4550 with
         | M t1 ->
             ((let uu____4553 = is_C t1 in
               if uu____4553 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____4557) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu____4563) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____4569, uu____4570) -> is_C t1
    | uu____4611 -> false
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      fun e ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk1 env t in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type in
        let body =
          let uu____4642 =
            let uu____4643 =
              let uu____4658 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4659 =
                let uu____4666 =
                  let uu____4671 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4671) in
                [uu____4666] in
              (uu____4658, uu____4659) in
            FStar_Syntax_Syntax.Tm_app uu____4643 in
          mk1 uu____4642 in
        let uu____4686 =
          let uu____4687 = FStar_Syntax_Syntax.mk_binder p in [uu____4687] in
        FStar_Syntax_Util.abs uu____4686 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.kprop))
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___73_4692 ->
    match uu___73_4692 with
    | FStar_Syntax_Syntax.Tm_unknown -> true
    | uu____4693 -> false
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      fun context_nm ->
        let return_if uu____4926 =
          match uu____4926 with
          | (rec_nm, s_e, u_e) ->
              let check1 t1 t2 =
                let uu____4957 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4959 =
                       let uu____4960 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4960 in
                     Prims.op_Negation uu____4959) in
                if uu____4957
                then
                  let uu____4961 =
                    let uu____4966 =
                      let uu____4967 = FStar_Syntax_Print.term_to_string e in
                      let uu____4968 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4969 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4967 uu____4968 uu____4969 in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4966) in
                  FStar_Errors.raise_err uu____4961
                else () in
              (match (rec_nm, context_nm) with
               | (N t1, N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1, M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1, M t2) ->
                   (check1 t1 t2;
                    (let uu____4986 = mk_return env t1 s_e in
                     ((M t1), uu____4986, u_e)))
               | (M t1, N t2) ->
                   let uu____4989 =
                     let uu____4994 =
                       let uu____4995 = FStar_Syntax_Print.term_to_string e in
                       let uu____4996 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4997 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4995 uu____4996 uu____4997 in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4994) in
                   FStar_Errors.raise_err uu____4989) in
        let ensure_m env1 e2 =
          let strip_m uu___74_5044 =
            match uu___74_5044 with
            | (M t, s_e, u_e) -> (t, s_e, u_e)
            | uu____5060 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____5080 =
                let uu____5085 =
                  let uu____5086 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____5086 in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____5085) in
              FStar_Errors.raise_error uu____5080 e2.FStar_Syntax_Syntax.pos
          | M uu____5093 ->
              let uu____5094 = check env1 e2 context_nm in strip_m uu____5094 in
        let uu____5101 =
          let uu____5102 = FStar_Syntax_Subst.compress e in
          uu____5102.FStar_Syntax_Syntax.n in
        match uu____5101 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5111 ->
            let uu____5112 = infer env e in return_if uu____5112
        | FStar_Syntax_Syntax.Tm_name uu____5119 ->
            let uu____5120 = infer env e in return_if uu____5120
        | FStar_Syntax_Syntax.Tm_fvar uu____5127 ->
            let uu____5128 = infer env e in return_if uu____5128
        | FStar_Syntax_Syntax.Tm_abs uu____5135 ->
            let uu____5152 = infer env e in return_if uu____5152
        | FStar_Syntax_Syntax.Tm_constant uu____5159 ->
            let uu____5160 = infer env e in return_if uu____5160
        | FStar_Syntax_Syntax.Tm_quoted uu____5167 ->
            let uu____5174 = infer env e in return_if uu____5174
        | FStar_Syntax_Syntax.Tm_app uu____5181 ->
            let uu____5196 = infer env e in return_if uu____5196
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5204 = FStar_Syntax_Util.unfold_lazy i in
            check env uu____5204 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
            mk_let env binding e2
              (fun env1 -> fun e21 -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0, branches) ->
            mk_match env e0 branches
              (fun env1 -> fun body -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1, uu____5266) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1, uu____5272) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1, uu____5278, uu____5279) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5320 ->
            let uu____5333 =
              let uu____5334 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5334 in
            failwith uu____5333
        | FStar_Syntax_Syntax.Tm_type uu____5341 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5348 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5367 ->
            let uu____5374 =
              let uu____5375 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5375 in
            failwith uu____5374
        | FStar_Syntax_Syntax.Tm_uvar uu____5382 ->
            let uu____5399 =
              let uu____5400 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5400 in
            failwith uu____5399
        | FStar_Syntax_Syntax.Tm_delayed uu____5407 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____5438 =
              let uu____5439 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5439 in
            failwith uu____5438
and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env in
      let uu____5467 =
        let uu____5468 = FStar_Syntax_Subst.compress e in
        uu____5468.FStar_Syntax_Syntax.n in
      match uu____5467 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5486 = FStar_Syntax_Util.unfold_lazy i in
          infer env uu____5486
      | FStar_Syntax_Syntax.Tm_abs (binders, body, rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5533;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None;
                  FStar_Syntax_Syntax.residual_flags = uu____5534;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5540 =
                  let uu___89_5541 = rc in
                  let uu____5542 =
                    let uu____5547 =
                      let uu____5548 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____5548 in
                    FStar_Pervasives_Native.Some uu____5547 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___89_5541.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5542;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___89_5541.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____5540 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___90_5558 = env in
            let uu____5559 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____5559;
              subst = (uu___90_5558.subst);
              tc_const = (uu___90_5558.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____5579 ->
                 match uu____5579 with
                 | (bv, qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___91_5592 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___91_5592.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___91_5592.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____5593 =
            FStar_List.fold_left
              (fun uu____5622 ->
                 fun uu____5623 ->
                   match (uu____5622, uu____5623) with
                   | ((env2, acc), (bv, qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5671 = is_C c in
                       if uu____5671
                       then
                         let xw =
                           let uu____5679 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5679 in
                         let x =
                           let uu___92_5681 = bv in
                           let uu____5682 =
                             let uu____5685 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5685 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___92_5681.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___92_5681.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5682
                           } in
                         let env3 =
                           let uu___93_5687 = env2 in
                           let uu____5688 =
                             let uu____5691 =
                               let uu____5692 =
                                 let uu____5699 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5699) in
                               FStar_Syntax_Syntax.NT uu____5692 in
                             uu____5691 :: (env2.subst) in
                           {
                             env = (uu___93_5687.env);
                             subst = uu____5688;
                             tc_const = (uu___93_5687.tc_const)
                           } in
                         let uu____5700 =
                           let uu____5703 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5704 =
                             let uu____5707 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5707 :: acc in
                           uu____5703 :: uu____5704 in
                         (env3, uu____5700)
                       else
                         (let x =
                            let uu___94_5712 = bv in
                            let uu____5713 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___94_5712.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___94_5712.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5713
                            } in
                          let uu____5716 =
                            let uu____5719 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5719 :: acc in
                          (env2, uu____5716))) (env1, []) binders1 in
          (match uu____5593 with
           | (env2, u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5739 =
                 let check_what =
                   let uu____5761 = is_monadic rc_opt1 in
                   if uu____5761 then check_m else check_n in
                 let uu____5775 = check_what env2 body1 in
                 match uu____5775 with
                 | (t, s_body, u_body) ->
                     let uu____5791 =
                       let uu____5792 =
                         let uu____5793 = is_monadic rc_opt1 in
                         if uu____5793 then M t else N t in
                       comp_of_nm uu____5792 in
                     (uu____5791, s_body, u_body) in
               (match uu____5739 with
                | (comp, s_body, u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None ->
                               let rc1 =
                                 let uu____5818 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___75_5822 ->
                                           match uu___75_5822 with
                                           | FStar_Syntax_Syntax.CPS -> true
                                           | uu____5823 -> false)) in
                                 if uu____5818
                                 then
                                   let uu____5824 =
                                     FStar_List.filter
                                       (fun uu___76_5828 ->
                                          match uu___76_5828 with
                                          | FStar_Syntax_Syntax.CPS -> false
                                          | uu____5829 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5824
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5838 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___77_5842 ->
                                         match uu___77_5842 with
                                         | FStar_Syntax_Syntax.CPS -> true
                                         | uu____5843 -> false)) in
                               if uu____5838
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___78_5850 ->
                                        match uu___78_5850 with
                                        | FStar_Syntax_Syntax.CPS -> false
                                        | uu____5851 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5852 =
                                   let uu____5853 =
                                     let uu____5858 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5858 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5853 flags1 in
                                 FStar_Pervasives_Native.Some uu____5852
                               else
                                 (let uu____5860 =
                                    let uu___95_5861 = rc in
                                    let uu____5862 =
                                      let uu____5867 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5867 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___95_5861.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5862;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___95_5861.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5860)) in
                    let uu____5868 =
                      let comp1 =
                        let uu____5878 = is_monadic rc_opt1 in
                        let uu____5879 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5878 uu____5879 in
                      let uu____5880 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5880,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5868 with
                     | (u_body1, u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5922 =
                             let uu____5923 =
                               let uu____5940 =
                                 let uu____5943 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5943 s_rc_opt in
                               (s_binders1, s_body1, uu____5940) in
                             FStar_Syntax_Syntax.Tm_abs uu____5923 in
                           mk1 uu____5922 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5953 =
                             let uu____5954 =
                               let uu____5971 =
                                 let uu____5974 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5974 u_rc_opt in
                               (u_binders2, u_body2, uu____5971) in
                             FStar_Syntax_Syntax.Tm_abs uu____5954 in
                           mk1 uu____5953 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5984;_};
            FStar_Syntax_Syntax.fv_delta = uu____5985;
            FStar_Syntax_Syntax.fv_qual = uu____5986;_}
          ->
          let uu____5989 =
            let uu____5994 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5994 in
          (match uu____5989 with
           | (uu____6025, t) ->
               let uu____6027 = let uu____6028 = normalize1 t in N uu____6028 in
               (uu____6027, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____6029;
             FStar_Syntax_Syntax.vars = uu____6030;_},
           a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____6093 = FStar_Syntax_Util.head_and_args e in
          (match uu____6093 with
           | (unary_op, uu____6115) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____6174;
             FStar_Syntax_Syntax.vars = uu____6175;_},
           a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____6251 = FStar_Syntax_Util.head_and_args e in
          (match uu____6251 with
           | (unary_op, uu____6273) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____6338;
             FStar_Syntax_Syntax.vars = uu____6339;_},
           (a, FStar_Pervasives_Native.None)::[])
          ->
          let uu____6377 = infer env a in
          (match uu____6377 with
           | (t, s, u) ->
               let uu____6393 = FStar_Syntax_Util.head_and_args e in
               (match uu____6393 with
                | (head1, uu____6415) ->
                    let uu____6436 =
                      let uu____6437 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____6437 in
                    let uu____6438 =
                      let uu____6441 =
                        let uu____6442 =
                          let uu____6457 =
                            let uu____6460 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6460] in
                          (head1, uu____6457) in
                        FStar_Syntax_Syntax.Tm_app uu____6442 in
                      mk1 uu____6441 in
                    let uu____6465 =
                      let uu____6468 =
                        let uu____6469 =
                          let uu____6484 =
                            let uu____6487 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6487] in
                          (head1, uu____6484) in
                        FStar_Syntax_Syntax.Tm_app uu____6469 in
                      mk1 uu____6468 in
                    (uu____6436, uu____6438, uu____6465)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____6496;
             FStar_Syntax_Syntax.vars = uu____6497;_},
           (a1, uu____6499)::a2::[])
          ->
          let uu____6541 = infer env a1 in
          (match uu____6541 with
           | (t, s, u) ->
               let uu____6557 = FStar_Syntax_Util.head_and_args e in
               (match uu____6557 with
                | (head1, uu____6579) ->
                    let uu____6600 =
                      let uu____6603 =
                        let uu____6604 =
                          let uu____6619 =
                            let uu____6622 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6622; a2] in
                          (head1, uu____6619) in
                        FStar_Syntax_Syntax.Tm_app uu____6604 in
                      mk1 uu____6603 in
                    let uu____6639 =
                      let uu____6642 =
                        let uu____6643 =
                          let uu____6658 =
                            let uu____6661 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6661; a2] in
                          (head1, uu____6658) in
                        FStar_Syntax_Syntax.Tm_app uu____6643 in
                      mk1 uu____6642 in
                    (t, uu____6600, uu____6639)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____6682;
             FStar_Syntax_Syntax.vars = uu____6683;_},
           uu____6684)
          ->
          let uu____6705 =
            let uu____6710 =
              let uu____6711 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6711 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6710) in
          FStar_Errors.raise_error uu____6705 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____6718;
             FStar_Syntax_Syntax.vars = uu____6719;_},
           uu____6720)
          ->
          let uu____6741 =
            let uu____6746 =
              let uu____6747 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6747 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6746) in
          FStar_Errors.raise_error uu____6741 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1, args) ->
          let uu____6776 = check_n env head1 in
          (match uu____6776 with
           | (t_head, s_head, u_head) ->
               let is_arrow t =
                 let uu____6798 =
                   let uu____6799 = FStar_Syntax_Subst.compress t in
                   uu____6799.FStar_Syntax_Syntax.n in
                 match uu____6798 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6802 -> true
                 | uu____6815 -> false in
               let rec flatten1 t =
                 let uu____6834 =
                   let uu____6835 = FStar_Syntax_Subst.compress t in
                   uu____6835.FStar_Syntax_Syntax.n in
                 match uu____6834 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,
                      {
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                          (t1, uu____6852);
                        FStar_Syntax_Syntax.pos = uu____6853;
                        FStar_Syntax_Syntax.vars = uu____6854;_})
                     when is_arrow t1 ->
                     let uu____6879 = flatten1 t1 in
                     (match uu____6879 with
                      | (binders', comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1, uu____6961, uu____6962) -> flatten1 e1
                 | uu____7003 ->
                     let uu____7004 =
                       let uu____7009 =
                         let uu____7010 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____7010 in
                       (FStar_Errors.Fatal_NotFunctionType, uu____7009) in
                     FStar_Errors.raise_err uu____7004 in
               let uu____7023 = flatten1 t_head in
               (match uu____7023 with
                | (binders, comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____7083 =
                          let uu____7088 =
                            let uu____7089 = FStar_Util.string_of_int n1 in
                            let uu____7096 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____7107 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____7089 uu____7096 uu____7107 in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____7088) in
                        FStar_Errors.raise_err uu____7083)
                     else ();
                     (let uu____7115 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____7115 with
                      | (binders1, comp1) ->
                          let rec final_type subst1 uu____7162 args1 =
                            match uu____7162 with
                            | (binders2, comp2) ->
                                (match (binders2, args1) with
                                 | ([], []) ->
                                     let uu____7236 =
                                       let uu____7237 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____7237.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____7236
                                 | (binders3, []) ->
                                     let uu____7267 =
                                       let uu____7268 =
                                         let uu____7271 =
                                           let uu____7272 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____7272 in
                                         FStar_Syntax_Subst.compress
                                           uu____7271 in
                                       uu____7268.FStar_Syntax_Syntax.n in
                                     (match uu____7267 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4, comp3) ->
                                          let uu____7297 =
                                            let uu____7298 =
                                              let uu____7299 =
                                                let uu____7312 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____7312) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____7299 in
                                            mk1 uu____7298 in
                                          N uu____7297
                                      | uu____7319 -> failwith "wat?")
                                 | ([], uu____7320::uu____7321) ->
                                     failwith "just checked that?!"
                                 | ((bv, uu____7361)::binders3,
                                    (arg, uu____7364)::args2) ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____7417 = FStar_List.splitAt n' binders1 in
                          (match uu____7417 with
                           | (binders2, uu____7449) ->
                               let uu____7474 =
                                 let uu____7495 =
                                   FStar_List.map2
                                     (fun uu____7549 ->
                                        fun uu____7550 ->
                                          match (uu____7549, uu____7550) with
                                          | ((bv, uu____7588), (arg, q)) ->
                                              let uu____7605 =
                                                let uu____7606 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____7606.FStar_Syntax_Syntax.n in
                                              (match uu____7605 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7625 ->
                                                   let uu____7626 =
                                                     let uu____7631 =
                                                       star_type' env arg in
                                                     (uu____7631, q) in
                                                   (uu____7626, [(arg, q)])
                                               | uu____7658 ->
                                                   let uu____7659 =
                                                     check_n env arg in
                                                   (match uu____7659 with
                                                    | (uu____7682, s_arg,
                                                       u_arg) ->
                                                        let uu____7685 =
                                                          let uu____7692 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7692
                                                          then
                                                            let uu____7699 =
                                                              let uu____7704
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7704, q) in
                                                            [uu____7699;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7685))))
                                     binders2 args in
                                 FStar_List.split uu____7495 in
                               (match uu____7474 with
                                | (s_args, u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7803 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7812 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7803, uu____7812)))))))
      | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0, branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1, uu____7880) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1, uu____7886) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1, uu____7892, uu____7893) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7935 = let uu____7936 = env.tc_const c in N uu____7936 in
          (uu____7935, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm, qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7943 ->
          let uu____7956 =
            let uu____7957 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7957 in
          failwith uu____7956
      | FStar_Syntax_Syntax.Tm_type uu____7964 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7971 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7990 ->
          let uu____7997 =
            let uu____7998 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7998 in
          failwith uu____7997
      | FStar_Syntax_Syntax.Tm_uvar uu____8005 ->
          let uu____8022 =
            let uu____8023 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____8023 in
          failwith uu____8022
      | FStar_Syntax_Syntax.Tm_delayed uu____8030 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____8061 =
            let uu____8062 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8062 in
          failwith uu____8061
and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
          FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (nm, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e0 ->
      fun branches ->
        fun f ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos in
          let uu____8109 = check_n env e0 in
          match uu____8109 with
          | (uu____8122, s_e0, u_e0) ->
              let uu____8125 =
                let uu____8154 =
                  FStar_List.map
                    (fun b ->
                       let uu____8215 = FStar_Syntax_Subst.open_branch b in
                       match uu____8215 with
                       | (pat, FStar_Pervasives_Native.None, body) ->
                           let env1 =
                             let uu___96_8257 = env in
                             let uu____8258 =
                               let uu____8259 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____8259 in
                             {
                               env = uu____8258;
                               subst = (uu___96_8257.subst);
                               tc_const = (uu___96_8257.tc_const)
                             } in
                           let uu____8262 = f env1 body in
                           (match uu____8262 with
                            | (nm, s_body, u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8334 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____8154 in
              (match uu____8125 with
               | (nms, branches1) ->
                   let t1 =
                     let uu____8436 = FStar_List.hd nms in
                     match uu____8436 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___79_8442 ->
                          match uu___79_8442 with
                          | M uu____8443 -> true
                          | uu____8444 -> false) nms in
                   let uu____8445 =
                     let uu____8482 =
                       FStar_List.map2
                         (fun nm ->
                            fun uu____8572 ->
                              match uu____8572 with
                              | (pat, guard, (s_body, u_body, original_body))
                                  ->
                                  (match (nm, has_m) with
                                   | (N t2, false) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2, true) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2, true) ->
                                       let uu____8749 =
                                         check env original_body (M t2) in
                                       (match uu____8749 with
                                        | (uu____8786, s_body1, u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8825, false) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____8482 in
                   (match uu____8445 with
                    | (nms1, s_branches, u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____9009 ->
                                 match uu____9009 with
                                 | (pat, guard, s_body) ->
                                     let s_body1 =
                                       let uu____9060 =
                                         let uu____9061 =
                                           let uu____9076 =
                                             let uu____9083 =
                                               let uu____9088 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____9089 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____9088, uu____9089) in
                                             [uu____9083] in
                                           (s_body, uu____9076) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____9061 in
                                       mk1 uu____9060 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____9121 =
                              let uu____9122 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9122] in
                            let uu____9123 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____9121 uu____9123
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.kprop)) in
                          let t1_star =
                            let uu____9129 =
                              let uu____9136 =
                                let uu____9137 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____9137 in
                              [uu____9136] in
                            let uu____9138 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.kprop in
                            FStar_Syntax_Util.arrow uu____9129 uu____9138 in
                          let uu____9141 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____9180 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____9141, uu____9180)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____9197 =
                             let uu____9200 =
                               let uu____9201 =
                                 let uu____9228 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____9228,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____9201 in
                             mk1 uu____9200 in
                           let uu____9265 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____9197, uu____9265))))
and (mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term,
                 FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
            ->
            (nm, FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun binding ->
      fun e2 ->
        fun proceed ->
          fun ensure_m ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos in
            let e1 = binding.FStar_Syntax_Syntax.lbdef in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname in
            let x_binders =
              let uu____9314 = FStar_Syntax_Syntax.mk_binder x in
              [uu____9314] in
            let uu____9315 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____9315 with
            | (x_binders1, e21) ->
                let uu____9328 = infer env e1 in
                (match uu____9328 with
                 | (N t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu____9345 = is_C t1 in
                       if uu____9345
                       then
                         let uu___97_9346 = binding in
                         let uu____9347 =
                           let uu____9350 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____9350 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___97_9346.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___97_9346.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9347;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___97_9346.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___97_9346.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___97_9346.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___97_9346.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding in
                     let env1 =
                       let uu___98_9353 = env in
                       let uu____9354 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___99_9356 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___99_9356.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___99_9356.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9354;
                         subst = (uu___98_9353.subst);
                         tc_const = (uu___98_9353.tc_const)
                       } in
                     let uu____9357 = proceed env1 e21 in
                     (match uu____9357 with
                      | (nm_rec, s_e2, u_e2) ->
                          let s_binding =
                            let uu___100_9374 = binding in
                            let uu____9375 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___100_9374.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___100_9374.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9375;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___100_9374.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___100_9374.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___100_9374.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___100_9374.FStar_Syntax_Syntax.lbpos)
                            } in
                          let uu____9378 =
                            let uu____9381 =
                              let uu____9382 =
                                let uu____9395 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___101_9405 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___101_9405.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___101_9405.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___101_9405.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___101_9405.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___101_9405.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___101_9405.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9395) in
                              FStar_Syntax_Syntax.Tm_let uu____9382 in
                            mk1 uu____9381 in
                          let uu____9406 =
                            let uu____9409 =
                              let uu____9410 =
                                let uu____9423 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___102_9433 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___102_9433.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___102_9433.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___102_9433.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___102_9433.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___102_9433.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___102_9433.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9423) in
                              FStar_Syntax_Syntax.Tm_let uu____9410 in
                            mk1 uu____9409 in
                          (nm_rec, uu____9378, uu____9406))
                 | (M t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu___103_9442 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___103_9442.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___103_9442.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___103_9442.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___103_9442.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___103_9442.FStar_Syntax_Syntax.lbpos)
                       } in
                     let env1 =
                       let uu___104_9444 = env in
                       let uu____9445 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___105_9447 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___105_9447.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___105_9447.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9445;
                         subst = (uu___104_9444.subst);
                         tc_const = (uu___104_9444.tc_const)
                       } in
                     let uu____9448 = ensure_m env1 e21 in
                     (match uu____9448 with
                      | (t2, s_e2, u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____9471 =
                              let uu____9472 =
                                let uu____9487 =
                                  let uu____9494 =
                                    let uu____9499 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____9500 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9499, uu____9500) in
                                  [uu____9494] in
                                (s_e2, uu____9487) in
                              FStar_Syntax_Syntax.Tm_app uu____9472 in
                            mk1 uu____9471 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.kprop)) in
                          let body =
                            let uu____9519 =
                              let uu____9520 =
                                let uu____9535 =
                                  let uu____9542 =
                                    let uu____9547 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____9547) in
                                  [uu____9542] in
                                (s_e1, uu____9535) in
                              FStar_Syntax_Syntax.Tm_app uu____9520 in
                            mk1 uu____9519 in
                          let uu____9562 =
                            let uu____9563 =
                              let uu____9564 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9564] in
                            FStar_Syntax_Util.abs uu____9563 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.kprop)) in
                          let uu____9565 =
                            let uu____9568 =
                              let uu____9569 =
                                let uu____9582 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___106_9592 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___106_9592.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___106_9592.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___106_9592.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___106_9592.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___106_9592.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___106_9592.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9582) in
                              FStar_Syntax_Syntax.Tm_let uu____9569 in
                            mk1 uu____9568 in
                          ((M t2), uu____9562, uu____9565)))
and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let mn =
        let uu____9604 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____9604 in
      let uu____9605 = check env e mn in
      match uu____9605 with
      | (N t, s_e, u_e) -> (t, s_e, u_e)
      | uu____9621 -> failwith "[check_n]: impossible"
and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let mn =
        let uu____9643 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____9643 in
      let uu____9644 = check env e mn in
      match uu____9644 with
      | (M t, s_e, u_e) -> (t, s_e, u_e)
      | uu____9660 -> failwith "[check_m]: impossible"
and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t
and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
  fun t ->
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
  = fun t -> FStar_Syntax_Util.comp_result t
and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun c ->
      fun wp ->
        (let uu____9690 =
           let uu____9691 = is_C c in Prims.op_Negation uu____9691 in
         if uu____9690 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____9701 =
           let uu____9702 = FStar_Syntax_Subst.compress c in
           uu____9702.FStar_Syntax_Syntax.n in
         match uu____9701 with
         | FStar_Syntax_Syntax.Tm_app (head1, args) ->
             let uu____9727 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9727 with
              | (wp_head, wp_args) ->
                  ((let uu____9765 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9779 =
                           let uu____9780 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9780 in
                         Prims.op_Negation uu____9779) in
                    if uu____9765 then failwith "mismatch" else ());
                   (let uu____9788 =
                      let uu____9789 =
                        let uu____9804 =
                          FStar_List.map2
                            (fun uu____9832 ->
                               fun uu____9833 ->
                                 match (uu____9832, uu____9833) with
                                 | ((arg, q), (wp_arg, q')) ->
                                     let print_implicit q1 =
                                       let uu____9872 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9872
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9875 =
                                           let uu____9880 =
                                             let uu____9881 =
                                               print_implicit q in
                                             let uu____9882 =
                                               print_implicit q' in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____9881 uu____9882 in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9880) in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9875)
                                      else ();
                                      (let uu____9884 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9884, q)))) args wp_args in
                        (head1, uu____9804) in
                      FStar_Syntax_Syntax.Tm_app uu____9789 in
                    mk1 uu____9788)))
         | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9918 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9918 with
              | (binders_orig, comp1) ->
                  let uu____9925 =
                    let uu____9940 =
                      FStar_List.map
                        (fun uu____9974 ->
                           match uu____9974 with
                           | (bv, q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9994 = is_C h in
                               if uu____9994
                               then
                                 let w' =
                                   let uu____10006 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____10006 in
                                 let uu____10007 =
                                   let uu____10014 =
                                     let uu____10021 =
                                       let uu____10026 =
                                         let uu____10027 =
                                           let uu____10028 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____10028 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____10027 in
                                       (uu____10026, q) in
                                     [uu____10021] in
                                   (w', q) :: uu____10014 in
                                 (w', uu____10007)
                               else
                                 (let x =
                                    let uu____10049 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____10049 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9940 in
                  (match uu____9925 with
                   | (bvs, binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____10104 =
                           let uu____10107 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____10107 in
                         FStar_Syntax_Subst.subst_comp uu____10104 comp1 in
                       let app =
                         let uu____10111 =
                           let uu____10112 =
                             let uu____10127 =
                               FStar_List.map
                                 (fun bv ->
                                    let uu____10142 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____10143 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____10142, uu____10143)) bvs in
                             (wp, uu____10127) in
                           FStar_Syntax_Syntax.Tm_app uu____10112 in
                         mk1 uu____10111 in
                       let comp3 =
                         let uu____10151 = type_of_comp comp2 in
                         let uu____10152 = is_monadic_comp comp2 in
                         trans_G env uu____10151 uu____10152 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e, uu____10154, uu____10155) ->
             trans_F_ env e wp
         | uu____10196 -> failwith "impossible trans_F_")
and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun h ->
      fun is_monadic1 ->
        fun wp ->
          if is_monadic1
          then
            let uu____10201 =
              let uu____10202 = star_type' env h in
              let uu____10205 =
                let uu____10214 =
                  let uu____10219 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____10219) in
                [uu____10214] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____10202;
                FStar_Syntax_Syntax.effect_args = uu____10205;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____10201
          else
            (let uu____10229 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____10229)
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
  fun env ->
    fun t -> let uu____10248 = n env.env t in star_type' env uu____10248
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun t -> let uu____10267 = n env.env t in check_n env uu____10267
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun c ->
      fun wp ->
        let uu____10283 = n env.env c in
        let uu____10284 = n env.env wp in
        trans_F_ env uu____10283 uu____10284