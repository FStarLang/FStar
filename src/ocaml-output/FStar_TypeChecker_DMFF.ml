open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> tcenv
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> subst
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> tc_const
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env1 -> fun tc_const -> { tcenv = env1; subst = []; tc_const }
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
  =
  fun env1 ->
    fun binders ->
      fun a ->
        fun wp_a ->
          fun ed ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env1 wp_a in
            let a1 =
              let uu___28_125 = a in
              let uu____126 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env1
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___28_125.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___28_125.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____126
              } in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s in
            (let uu____136 =
               FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
             if uu____136
             then
               (d "Elaborating extra WP combinators";
                (let uu____138 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____138))
             else ());
            (let rec collect_binders t =
               let t1 = FStar_Syntax_Util.unascribe t in
               let uu____155 =
                 let uu____156 = FStar_Syntax_Subst.compress t1 in
                 uu____156.FStar_Syntax_Syntax.n in
               match uu____155 with
               | FStar_Syntax_Syntax.Tm_arrow (bs, comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t2, uu____191) -> t2
                     | uu____200 ->
                         let uu____201 =
                           let uu____206 =
                             let uu____207 =
                               FStar_Syntax_Print.comp_to_string comp in
                             FStar_Util.format1
                               "wp_a contains non-Tot arrow: %s" uu____207 in
                           (FStar_Errors.Error_UnexpectedDM4FType, uu____206) in
                         FStar_Errors.raise_error uu____201
                           comp.FStar_Syntax_Syntax.pos in
                   let uu____208 = collect_binders rest in
                   FStar_List.append bs uu____208
               | FStar_Syntax_Syntax.Tm_type uu____223 -> []
               | uu____230 ->
                   let uu____231 =
                     let uu____236 =
                       let uu____237 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Util.format1
                         "wp_a doesn't end in Type0, but rather in %s"
                         uu____237 in
                     (FStar_Errors.Error_UnexpectedDM4FType, uu____236) in
                   FStar_Errors.raise_error uu____231
                     t1.FStar_Syntax_Syntax.pos in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____261 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____261 FStar_Syntax_Util.name_binders in
             (let uu____287 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
              if uu____287
              then
                let uu____288 =
                  let uu____289 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____289 in
                d uu____288
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk x = FStar_Syntax_Syntax.mk x FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env2 lident def =
                let uu____323 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env2 lident
                    def in
                match uu____323 with
                | (sigelt, fv) ->
                    ((let uu____331 =
                        let uu____334 = FStar_ST.op_Bang sigelts in sigelt ::
                          uu____334 in
                      FStar_ST.op_Colon_Equals sigelts uu____331);
                     fv) in
              let binders_of_list =
                FStar_List.map
                  (fun uu____386 ->
                     match uu____386 with
                     | (t, b) ->
                         let uu____397 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____397)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t ->
                     let uu____436 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____436)) in
              let args_of_binders =
                FStar_List.map
                  (fun bv ->
                     let uu____469 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____469) in
              let uu____472 =
                let uu____489 =
                  let mk1 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____513 =
                        let uu____516 = FStar_Syntax_Syntax.bv_to_name t in
                        f uu____516 in
                      FStar_Syntax_Util.arrow gamma uu____513 in
                    let uu____517 =
                      let uu____518 =
                        let uu____527 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____534 =
                          let uu____543 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____543] in
                        uu____527 :: uu____534 in
                      FStar_List.append binders uu____518 in
                    FStar_Syntax_Util.abs uu____517 body
                      FStar_Pervasives_Native.None in
                  let uu____574 = mk1 FStar_Syntax_Syntax.mk_Total in
                  let uu____575 = mk1 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____574, uu____575) in
                match uu____489 with
                | (ctx_def, gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env1 ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env1 gctx_lid gctx_def in
                    let mk_app fv t =
                      let uu____615 =
                        let uu____616 =
                          let uu____633 =
                            let uu____644 =
                              FStar_List.map
                                (fun uu____666 ->
                                   match uu____666 with
                                   | (bv, uu____678) ->
                                       let uu____683 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____684 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____683, uu____684)) binders in
                            let uu____685 =
                              let uu____692 =
                                let uu____697 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____698 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____697, uu____698) in
                              let uu____699 =
                                let uu____706 =
                                  let uu____711 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____711) in
                                [uu____706] in
                              uu____692 :: uu____699 in
                            FStar_List.append uu____644 uu____685 in
                          (fv, uu____633) in
                        FStar_Syntax_Syntax.Tm_app uu____616 in
                      mk uu____615 in
                    (env1, (mk_app ctx_fv), (mk_app gctx_fv)) in
              match uu____472 with
              | (env2, mk_ctx, mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____782 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____782 in
                    let ret =
                      let uu____786 =
                        let uu____787 =
                          let uu____790 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____790 in
                        FStar_Syntax_Util.residual_tot uu____787 in
                      FStar_Pervasives_Native.Some uu____786 in
                    let body =
                      let uu____794 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____794 ret in
                    let uu____797 =
                      let uu____798 = mk_all_implicit binders in
                      let uu____805 =
                        binders_of_list [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____798 uu____805 in
                    FStar_Syntax_Util.abs uu____797 body ret in
                  let c_pure1 =
                    let uu____833 = mk_lid "pure" in
                    register env2 uu____833 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____840 =
                        let uu____841 =
                          let uu____842 =
                            let uu____851 =
                              let uu____858 =
                                let uu____859 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____859 in
                              FStar_Syntax_Syntax.mk_binder uu____858 in
                            [uu____851] in
                          let uu____872 =
                            let uu____875 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____875 in
                          FStar_Syntax_Util.arrow uu____842 uu____872 in
                        mk_gctx uu____841 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____840 in
                    let r =
                      let uu____877 =
                        let uu____878 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____878 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____877 in
                    let ret =
                      let uu____882 =
                        let uu____883 =
                          let uu____886 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____886 in
                        FStar_Syntax_Util.residual_tot uu____883 in
                      FStar_Pervasives_Native.Some uu____882 in
                    let outer_body =
                      let gamma_as_args = args_of_binders gamma in
                      let inner_body =
                        let uu____896 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____899 =
                          let uu____910 =
                            let uu____913 =
                              let uu____914 =
                                let uu____915 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____915
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____914 in
                            [uu____913] in
                          FStar_List.append gamma_as_args uu____910 in
                        FStar_Syntax_Util.mk_app uu____896 uu____899 in
                      FStar_Syntax_Util.abs gamma inner_body ret in
                    let uu____918 =
                      let uu____919 = mk_all_implicit binders in
                      let uu____926 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____919 uu____926 in
                    FStar_Syntax_Util.abs uu____918 outer_body ret in
                  let c_app1 =
                    let uu____962 = mk_lid "app" in
                    register env2 uu____962 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____971 =
                        let uu____980 =
                          let uu____987 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____987 in
                        [uu____980] in
                      let uu____1000 =
                        let uu____1003 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1003 in
                      FStar_Syntax_Util.arrow uu____971 uu____1000 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1006 =
                        let uu____1007 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1007 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1006 in
                    let ret =
                      let uu____1011 =
                        let uu____1012 =
                          let uu____1015 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1015 in
                        FStar_Syntax_Util.residual_tot uu____1012 in
                      FStar_Pervasives_Native.Some uu____1011 in
                    let uu____1016 =
                      let uu____1017 = mk_all_implicit binders in
                      let uu____1024 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____1017 uu____1024 in
                    let uu____1059 =
                      let uu____1062 =
                        let uu____1073 =
                          let uu____1076 =
                            let uu____1077 =
                              let uu____1088 =
                                let uu____1091 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____1091] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1088 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1077 in
                          let uu____1100 =
                            let uu____1103 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____1103] in
                          uu____1076 :: uu____1100 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1073 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1062 in
                    FStar_Syntax_Util.abs uu____1016 uu____1059 ret in
                  let c_lift11 =
                    let uu____1113 = mk_lid "lift1" in
                    register env2 uu____1113 c_lift1 in
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
                      let uu____1123 =
                        let uu____1132 =
                          let uu____1139 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1139 in
                        let uu____1140 =
                          let uu____1149 =
                            let uu____1156 =
                              FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____1156 in
                          [uu____1149] in
                        uu____1132 :: uu____1140 in
                      let uu____1175 =
                        let uu____1178 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1178 in
                      FStar_Syntax_Util.arrow uu____1123 uu____1175 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1181 =
                        let uu____1182 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1182 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1181 in
                    let a2 =
                      let uu____1184 =
                        let uu____1185 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____1185 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1184 in
                    let ret =
                      let uu____1189 =
                        let uu____1190 =
                          let uu____1193 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____1193 in
                        FStar_Syntax_Util.residual_tot uu____1190 in
                      FStar_Pervasives_Native.Some uu____1189 in
                    let uu____1194 =
                      let uu____1195 = mk_all_implicit binders in
                      let uu____1202 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1195 uu____1202 in
                    let uu____1245 =
                      let uu____1248 =
                        let uu____1259 =
                          let uu____1262 =
                            let uu____1263 =
                              let uu____1274 =
                                let uu____1277 =
                                  let uu____1278 =
                                    let uu____1289 =
                                      let uu____1292 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1292] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1289 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1278 in
                                let uu____1301 =
                                  let uu____1304 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1304] in
                                uu____1277 :: uu____1301 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1274 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1263 in
                          let uu____1313 =
                            let uu____1316 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1316] in
                          uu____1262 :: uu____1313 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1259 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1248 in
                    FStar_Syntax_Util.abs uu____1194 uu____1245 ret in
                  let c_lift21 =
                    let uu____1326 = mk_lid "lift2" in
                    register env2 uu____1326 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1335 =
                        let uu____1344 =
                          let uu____1351 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1351 in
                        [uu____1344] in
                      let uu____1364 =
                        let uu____1367 =
                          let uu____1368 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1368 in
                        FStar_Syntax_Syntax.mk_Total uu____1367 in
                      FStar_Syntax_Util.arrow uu____1335 uu____1364 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret =
                      let uu____1373 =
                        let uu____1374 =
                          let uu____1377 =
                            let uu____1378 =
                              let uu____1387 =
                                let uu____1394 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1394 in
                              [uu____1387] in
                            let uu____1407 =
                              let uu____1410 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1410 in
                            FStar_Syntax_Util.arrow uu____1378 uu____1407 in
                          mk_ctx uu____1377 in
                        FStar_Syntax_Util.residual_tot uu____1374 in
                      FStar_Pervasives_Native.Some uu____1373 in
                    let e1 =
                      let uu____1412 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1412 in
                    let body =
                      let uu____1416 =
                        let uu____1417 =
                          let uu____1426 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1426] in
                        FStar_List.append gamma uu____1417 in
                      let uu____1451 =
                        let uu____1454 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1457 =
                          let uu____1468 =
                            let uu____1469 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1469 in
                          let uu____1470 = args_of_binders gamma in
                          uu____1468 :: uu____1470 in
                        FStar_Syntax_Util.mk_app uu____1454 uu____1457 in
                      FStar_Syntax_Util.abs uu____1416 uu____1451 ret in
                    let uu____1473 =
                      let uu____1474 = mk_all_implicit binders in
                      let uu____1481 =
                        binders_of_list
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1474 uu____1481 in
                    FStar_Syntax_Util.abs uu____1473 body ret in
                  let c_push1 =
                    let uu____1513 = mk_lid "push" in
                    register env2 uu____1513 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > Prims.int_zero
                    then
                      let uu____1537 =
                        let uu____1538 =
                          let uu____1555 = args_of_binders binders in
                          (c, uu____1555) in
                        FStar_Syntax_Syntax.Tm_app uu____1538 in
                      mk uu____1537
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1583 =
                        let uu____1584 =
                          let uu____1593 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1600 =
                            let uu____1609 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1609] in
                          uu____1593 :: uu____1600 in
                        let uu____1634 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1584 uu____1634 in
                      FStar_Syntax_Syntax.mk_Total uu____1583 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1638 =
                      let uu____1639 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1639 in
                    let uu____1654 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.of_int (2))) FStar_Pervasives_Native.None in
                      let uu____1658 =
                        let uu____1661 =
                          let uu____1672 =
                            let uu____1675 =
                              let uu____1676 =
                                let uu____1687 =
                                  let uu____1696 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1696 in
                                [uu____1687] in
                              FStar_Syntax_Util.mk_app l_ite uu____1676 in
                            [uu____1675] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1672 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1661 in
                      FStar_Syntax_Util.ascribe uu____1658
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1638 uu____1654
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1740 = mk_lid "wp_if_then_else" in
                    register env2 uu____1740 wp_if_then_else in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1751 =
                        let uu____1760 =
                          let uu____1767 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1767 in
                        [uu____1760] in
                      let uu____1780 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1751 uu____1780 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1787 =
                        let uu____1798 =
                          let uu____1801 =
                            let uu____1802 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1802 in
                          let uu____1821 =
                            let uu____1824 =
                              let uu____1825 =
                                let uu____1836 =
                                  let uu____1839 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1839] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1836 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1825 in
                            [uu____1824] in
                          uu____1801 :: uu____1821 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1798 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1787 in
                    let uu____1856 =
                      let uu____1857 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1857 in
                    FStar_Syntax_Util.abs uu____1856 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1873 = mk_lid "wp_close" in
                    register env2 uu____1873 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1883 =
                      let uu____1884 =
                        let uu____1885 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left
                          FStar_TypeChecker_Common.lcomp_of_comp uu____1885 in
                      FStar_TypeChecker_Common.residual_comp_of_lcomp
                        uu____1884 in
                    FStar_Pervasives_Native.Some uu____1883 in
                  let mk_forall x body =
                    let uu____1897 =
                      let uu____1898 =
                        let uu____1915 =
                          let uu____1926 =
                            let uu____1935 =
                              let uu____1936 =
                                let uu____1937 =
                                  FStar_Syntax_Syntax.mk_binder x in
                                [uu____1937] in
                              FStar_Syntax_Util.abs uu____1936 body
                                ret_tot_type in
                            FStar_Syntax_Syntax.as_arg uu____1935 in
                          [uu____1926] in
                        (FStar_Syntax_Util.tforall, uu____1915) in
                      FStar_Syntax_Syntax.Tm_app uu____1898 in
                    FStar_Syntax_Syntax.mk uu____1897 FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1994 =
                      let uu____1995 = FStar_Syntax_Subst.compress t in
                      uu____1995.FStar_Syntax_Syntax.n in
                    match uu____1994 with
                    | FStar_Syntax_Syntax.Tm_type uu____1998 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu____2030 ->
                              match uu____2030 with
                              | (b, uu____2038) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2043 -> true in
                  let rec is_monotonic t =
                    let uu____2054 =
                      let uu____2055 = FStar_Syntax_Subst.compress t in
                      uu____2055.FStar_Syntax_Syntax.n in
                    match uu____2054 with
                    | FStar_Syntax_Syntax.Tm_type uu____2058 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu____2090 ->
                              match uu____2090 with
                              | (b, uu____2098) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2103 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env2 t in
                    let uu____2177 =
                      let uu____2178 = FStar_Syntax_Subst.compress t1 in
                      uu____2178.FStar_Syntax_Syntax.n in
                    match uu____2177 with
                    | FStar_Syntax_Syntax.Tm_type uu____2183 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                             (b, uu____2186);
                           FStar_Syntax_Syntax.pos = uu____2187;
                           FStar_Syntax_Syntax.vars = uu____2188;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2232 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2232
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2239 =
                              let uu____2242 =
                                let uu____2253 =
                                  let uu____2262 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2262 in
                                [uu____2253] in
                              FStar_Syntax_Util.mk_app x uu____2242 in
                            let uu____2279 =
                              let uu____2282 =
                                let uu____2293 =
                                  let uu____2302 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2302 in
                                [uu____2293] in
                              FStar_Syntax_Util.mk_app y uu____2282 in
                            mk_rel1 b uu____2239 uu____2279 in
                          mk_forall a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2323 =
                               let uu____2326 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2329 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2326 uu____2329 in
                             let uu____2332 =
                               let uu____2335 =
                                 let uu____2338 =
                                   let uu____2349 =
                                     let uu____2358 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2358 in
                                   [uu____2349] in
                                 FStar_Syntax_Util.mk_app x uu____2338 in
                               let uu____2375 =
                                 let uu____2378 =
                                   let uu____2389 =
                                     let uu____2398 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2398 in
                                   [uu____2389] in
                                 FStar_Syntax_Util.mk_app y uu____2378 in
                               mk_rel1 b uu____2335 uu____2375 in
                             FStar_Syntax_Util.mk_imp uu____2323 uu____2332 in
                           let uu____2415 = mk_forall a21 body in
                           mk_forall a11 uu____2415)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                             (b, uu____2418);
                           FStar_Syntax_Syntax.pos = uu____2419;
                           FStar_Syntax_Syntax.vars = uu____2420;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2464 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2464
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2471 =
                              let uu____2474 =
                                let uu____2485 =
                                  let uu____2494 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2494 in
                                [uu____2485] in
                              FStar_Syntax_Util.mk_app x uu____2474 in
                            let uu____2511 =
                              let uu____2514 =
                                let uu____2525 =
                                  let uu____2534 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2534 in
                                [uu____2525] in
                              FStar_Syntax_Util.mk_app y uu____2514 in
                            mk_rel1 b uu____2471 uu____2511 in
                          mk_forall a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2555 =
                               let uu____2558 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2561 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2558 uu____2561 in
                             let uu____2564 =
                               let uu____2567 =
                                 let uu____2570 =
                                   let uu____2581 =
                                     let uu____2590 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2590 in
                                   [uu____2581] in
                                 FStar_Syntax_Util.mk_app x uu____2570 in
                               let uu____2607 =
                                 let uu____2610 =
                                   let uu____2621 =
                                     let uu____2630 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2630 in
                                   [uu____2621] in
                                 FStar_Syntax_Util.mk_app y uu____2610 in
                               mk_rel1 b uu____2567 uu____2607 in
                             FStar_Syntax_Util.mk_imp uu____2555 uu____2564 in
                           let uu____2647 = mk_forall a21 body in
                           mk_forall a11 uu____2647)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1, comp)
                        ->
                        let t2 =
                          let uu___229_2686 = t1 in
                          let uu____2687 =
                            let uu____2688 =
                              let uu____2703 =
                                let uu____2706 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2706 in
                              ([binder], uu____2703) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2688 in
                          {
                            FStar_Syntax_Syntax.n = uu____2687;
                            FStar_Syntax_Syntax.pos =
                              (uu___229_2686.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___229_2686.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow ([], uu____2729) ->
                        failwith "impossible: arrow with empty binders"
                    | uu____2750 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                          [FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env2 t in
                      let uu____2785 =
                        let uu____2786 = FStar_Syntax_Subst.compress t1 in
                        uu____2786.FStar_Syntax_Syntax.n in
                      match uu____2785 with
                      | FStar_Syntax_Syntax.Tm_type uu____2789 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head, args) when
                          let uu____2816 = FStar_Syntax_Subst.compress head in
                          FStar_Syntax_Util.is_tuple_constructor uu____2816
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2835 =
                                let uu____2836 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env2
                                  uu____2836 i in
                              FStar_Syntax_Syntax.fvar uu____2835
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   Prims.int_one)
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2865 =
                            let uu____2876 =
                              FStar_List.mapi
                                (fun i ->
                                   fun uu____2894 ->
                                     match uu____2894 with
                                     | (t2, q) ->
                                         let uu____2913 = project i x in
                                         let uu____2916 = project i y in
                                         mk_stronger t2 uu____2913 uu____2916)
                                args in
                            match uu____2876 with
                            | [] ->
                                failwith
                                  "Impossible: empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2865 with
                           | (rel0, rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (b, uu____2969);
                             FStar_Syntax_Syntax.pos = uu____2970;
                             FStar_Syntax_Syntax.vars = uu____2971;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu____3015 ->
                                   match uu____3015 with
                                   | (bv, q) ->
                                       let uu____3028 =
                                         let uu____3029 =
                                           FStar_Util.string_of_int i in
                                         Prims.op_Hat "a" uu____3029 in
                                       FStar_Syntax_Syntax.gen_bv uu____3028
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu____3036 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____3036) bvs in
                          let body =
                            let uu____3038 = FStar_Syntax_Util.mk_app x args in
                            let uu____3041 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____3038 uu____3041 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall bv body1) bvs
                            body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Total (b, uu____3050);
                             FStar_Syntax_Syntax.pos = uu____3051;
                             FStar_Syntax_Syntax.vars = uu____3052;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu____3096 ->
                                   match uu____3096 with
                                   | (bv, q) ->
                                       let uu____3109 =
                                         let uu____3110 =
                                           FStar_Util.string_of_int i in
                                         Prims.op_Hat "a" uu____3110 in
                                       FStar_Syntax_Syntax.gen_bv uu____3109
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu____3117 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____3117) bvs in
                          let body =
                            let uu____3119 = FStar_Syntax_Util.mk_app x args in
                            let uu____3122 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____3119 uu____3122 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall bv body1) bvs
                            body
                      | uu____3129 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____3131 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____3134 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____3137 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____3131 uu____3134 uu____3137 in
                    let uu____3140 =
                      let uu____3141 =
                        binders_of_list
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____3141 in
                    FStar_Syntax_Util.abs uu____3140 body ret_tot_type in
                  let stronger1 =
                    let uu____3173 = mk_lid "stronger" in
                    register env2 uu____3173 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____3179 = FStar_Util.prefix gamma in
                    match uu____3179 with
                    | (wp_args, post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq =
                            let uu____3244 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3244 in
                          let uu____3249 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq in
                          match uu____3249 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1, [], body))
                              ->
                              let k_app =
                                let uu____3259 = args_of_binders binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____3259 in
                              let guard_free =
                                let uu____3271 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____3271 in
                              let pat =
                                let uu____3275 =
                                  let uu____3286 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____3286] in
                                FStar_Syntax_Util.mk_app guard_free
                                  uu____3275 in
                              let pattern_guarded_body =
                                let uu____3314 =
                                  let uu____3315 =
                                    let uu____3322 =
                                      let uu____3323 =
                                        let uu____3344 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1 in
                                        let uu____3349 =
                                          let uu____3362 =
                                            let uu____3373 =
                                              FStar_Syntax_Syntax.as_arg pat in
                                            [uu____3373] in
                                          [uu____3362] in
                                        (uu____3344, uu____3349) in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3323 in
                                    (body, uu____3322) in
                                  FStar_Syntax_Syntax.Tm_meta uu____3315 in
                                mk uu____3314 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3436 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____3444 =
                            let uu____3447 =
                              let uu____3448 =
                                let uu____3451 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____3454 =
                                  let uu____3465 = args_of_binders wp_args in
                                  let uu____3468 =
                                    let uu____3471 =
                                      let uu____3472 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____3472 in
                                    [uu____3471] in
                                  FStar_List.append uu____3465 uu____3468 in
                                FStar_Syntax_Util.mk_app uu____3451
                                  uu____3454 in
                              FStar_Syntax_Util.mk_imp equiv uu____3448 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3447 in
                          FStar_Syntax_Util.abs gamma uu____3444
                            ret_gtot_type in
                        let uu____3473 =
                          let uu____3474 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____3474 in
                        FStar_Syntax_Util.abs uu____3473 body ret_gtot_type in
                  let ite_wp1 =
                    let uu____3490 = mk_lid "ite_wp" in
                    register env2 uu____3490 ite_wp in
                  let ite_wp2 = mk_generic_app ite_wp1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____3496 = FStar_Util.prefix gamma in
                    match uu____3496 with
                    | (wp_args, post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____3553 =
                            let uu____3554 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____3561 =
                              let uu____3572 =
                                let uu____3581 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____3581 in
                              [uu____3572] in
                            FStar_Syntax_Util.mk_app uu____3554 uu____3561 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3553 in
                        let uu____3598 =
                          let uu____3599 =
                            let uu____3608 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____3608 gamma in
                          FStar_List.append binders uu____3599 in
                        FStar_Syntax_Util.abs uu____3598 body ret_gtot_type in
                  let null_wp1 =
                    let uu____3630 = mk_lid "null_wp" in
                    register env2 uu____3630 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____3641 =
                        let uu____3652 =
                          let uu____3655 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____3656 =
                            let uu____3659 =
                              let uu____3660 =
                                let uu____3671 =
                                  let uu____3680 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____3680 in
                                [uu____3671] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3660 in
                            let uu____3697 =
                              let uu____3700 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____3700] in
                            uu____3659 :: uu____3697 in
                          uu____3655 :: uu____3656 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3652 in
                      FStar_Syntax_Util.mk_app stronger2 uu____3641 in
                    let uu____3709 =
                      let uu____3710 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____3710 in
                    FStar_Syntax_Util.abs uu____3709 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____3726 = mk_lid "wp_trivial" in
                    register env2 uu____3726 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____3731 =
                      FStar_TypeChecker_Env.debug env2
                        (FStar_Options.Other "ED") in
                    if uu____3731
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let ed_combs =
                      match ed.FStar_Syntax_Syntax.combinators with
                      | FStar_Syntax_Syntax.DM4F_eff combs ->
                          let uu____3740 =
                            let uu___340_3741 = combs in
                            let uu____3742 =
                              let uu____3743 = c stronger2 in
                              ([], uu____3743) in
                            let uu____3750 =
                              let uu____3751 = c wp_if_then_else2 in
                              ([], uu____3751) in
                            let uu____3758 =
                              let uu____3759 = c ite_wp2 in ([], uu____3759) in
                            let uu____3766 =
                              let uu____3767 = c wp_close2 in
                              ([], uu____3767) in
                            let uu____3774 =
                              let uu____3775 = c wp_trivial2 in
                              ([], uu____3775) in
                            {
                              FStar_Syntax_Syntax.ret_wp =
                                (uu___340_3741.FStar_Syntax_Syntax.ret_wp);
                              FStar_Syntax_Syntax.bind_wp =
                                (uu___340_3741.FStar_Syntax_Syntax.bind_wp);
                              FStar_Syntax_Syntax.stronger = uu____3742;
                              FStar_Syntax_Syntax.if_then_else = uu____3750;
                              FStar_Syntax_Syntax.ite_wp = uu____3758;
                              FStar_Syntax_Syntax.close_wp = uu____3766;
                              FStar_Syntax_Syntax.trivial = uu____3774;
                              FStar_Syntax_Syntax.repr =
                                (uu___340_3741.FStar_Syntax_Syntax.repr);
                              FStar_Syntax_Syntax.return_repr =
                                (uu___340_3741.FStar_Syntax_Syntax.return_repr);
                              FStar_Syntax_Syntax.bind_repr =
                                (uu___340_3741.FStar_Syntax_Syntax.bind_repr)
                            } in
                          FStar_Syntax_Syntax.DM4F_eff uu____3740
                      | uu____3782 ->
                          failwith
                            "Impossible! For a DM4F effect combinators must be in DM4f_eff" in
                    let uu____3783 =
                      let uu____3784 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____3784 in
                    (uu____3783,
                      (let uu___344_3798 = ed in
                       {
                         FStar_Syntax_Syntax.mname =
                           (uu___344_3798.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___344_3798.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.univs =
                           (uu___344_3798.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___344_3798.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature =
                           (uu___344_3798.FStar_Syntax_Syntax.signature);
                         FStar_Syntax_Syntax.combinators = ed_combs;
                         FStar_Syntax_Syntax.actions =
                           (uu___344_3798.FStar_Syntax_Syntax.actions);
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___344_3798.FStar_Syntax_Syntax.eff_attrs)
                       }))))))
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env1 -> env1.tcenv
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env ->
    fun env' ->
      let uu___349_3814 = dmff_env in
      {
        tcenv = env';
        subst = (uu___349_3814.subst);
        tc_const = (uu___349_3814.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee -> match projectee with | N _0 -> true | uu____3831 -> false
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | N _0 -> _0
let (uu___is_M : nm -> Prims.bool) =
  fun projectee -> match projectee with | M _0 -> true | uu____3844 -> false
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | M _0 -> _0
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____3861) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_3874 ->
                match uu___0_3874 with
                | FStar_Syntax_Syntax.CPS -> true
                | uu____3875 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____3876 ->
        let uu____3877 =
          let uu____3882 =
            let uu____3883 = FStar_Syntax_Print.comp_to_string c in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____3883 in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____3882) in
        FStar_Errors.raise_error uu____3877 c.FStar_Syntax_Syntax.pos
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_3888 ->
    match uu___1_3888 with
    | N t ->
        let uu____3890 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____3890
    | M t ->
        let uu____3892 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____3892
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n ->
    match n with
    | FStar_Syntax_Syntax.Tm_arrow (uu____3898, c) -> nm_of_comp c
    | uu____3920 -> failwith "unexpected_argument: [is_monadic_arrow]"
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    let uu____3930 = nm_of_comp c in
    match uu____3930 with | M uu____3931 -> true | N uu____3932 -> false
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Not_found -> true | uu____3938 -> false
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ ->
    let star_once typ1 =
      let uu____3952 =
        let uu____3961 =
          let uu____3968 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3968 in
        [uu____3961] in
      let uu____3987 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____3952 uu____3987 in
    let uu____3990 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____3990
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk ->
    fun env1 ->
      fun a ->
        let uu____4031 =
          let uu____4032 =
            let uu____4047 =
              let uu____4056 =
                let uu____4063 =
                  let uu____4064 = star_type' env1 a in
                  FStar_Syntax_Syntax.null_bv uu____4064 in
                let uu____4065 = FStar_Syntax_Syntax.as_implicit false in
                (uu____4063, uu____4065) in
              [uu____4056] in
            let uu____4082 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
            (uu____4047, uu____4082) in
          FStar_Syntax_Syntax.Tm_arrow uu____4032 in
        mk uu____4031
and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders, uu____4122) ->
          let binders1 =
            FStar_List.map
              (fun uu____4168 ->
                 match uu____4168 with
                 | (bv, aqual) ->
                     let uu____4187 =
                       let uu___399_4188 = bv in
                       let uu____4189 =
                         star_type' env1 bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___399_4188.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___399_4188.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____4189
                       } in
                     (uu____4187, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____4194,
                {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                    (hn, uu____4196);
                  FStar_Syntax_Syntax.pos = uu____4197;
                  FStar_Syntax_Syntax.vars = uu____4198;_})
               ->
               let uu____4227 =
                 let uu____4228 =
                   let uu____4243 =
                     let uu____4246 = star_type' env1 hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____4246 in
                   (binders1, uu____4243) in
                 FStar_Syntax_Syntax.Tm_arrow uu____4228 in
               mk uu____4227
           | uu____4257 ->
               let uu____4258 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____4258 with
                | N hn ->
                    let uu____4260 =
                      let uu____4261 =
                        let uu____4276 =
                          let uu____4279 = star_type' env1 hn in
                          FStar_Syntax_Syntax.mk_Total uu____4279 in
                        (binders1, uu____4276) in
                      FStar_Syntax_Syntax.Tm_arrow uu____4261 in
                    mk uu____4260
                | M a ->
                    let uu____4291 =
                      let uu____4292 =
                        let uu____4307 =
                          let uu____4316 =
                            let uu____4325 =
                              let uu____4332 =
                                let uu____4333 = mk_star_to_type1 env1 a in
                                FStar_Syntax_Syntax.null_bv uu____4333 in
                              let uu____4334 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____4332, uu____4334) in
                            [uu____4325] in
                          FStar_List.append binders1 uu____4316 in
                        let uu____4357 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____4307, uu____4357) in
                      FStar_Syntax_Syntax.Tm_arrow uu____4292 in
                    mk uu____4291))
      | FStar_Syntax_Syntax.Tm_app (head, args) ->
          let debug t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____4445 = f x in
                    FStar_Util.string_builder_append strb uu____4445);
                   FStar_List.iter
                     (fun x1 ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____4452 = f x1 in
                         FStar_Util.string_builder_append strb uu____4452))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____4454 =
              let uu____4459 =
                let uu____4460 = FStar_Syntax_Print.term_to_string t2 in
                let uu____4461 =
                  string_of_set FStar_Syntax_Print.bv_to_string s in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____4460 uu____4461 in
              (FStar_Errors.Warning_DependencyFound, uu____4459) in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____4454 in
          let rec is_non_dependent_arrow ty n =
            let uu____4477 =
              let uu____4478 = FStar_Syntax_Subst.compress ty in
              uu____4478.FStar_Syntax_Syntax.n in
            match uu____4477 with
            | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
                let uu____4503 =
                  let uu____4504 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____4504 in
                if uu____4503
                then false
                else
                  (try
                     (fun uu___448_4515 ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____4538 = FStar_Syntax_Free.names ty1 in
                                FStar_Util.set_intersect uu____4538 s in
                              let uu____4541 =
                                let uu____4542 =
                                  FStar_Util.set_is_empty sinter in
                                Prims.op_Negation uu____4542 in
                              if uu____4541
                              then
                                (debug ty1 sinter; FStar_Exn.raise Not_found)
                              else () in
                            let uu____4545 =
                              FStar_Syntax_Subst.open_comp binders c in
                            (match uu____4545 with
                             | (binders1, c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s ->
                                        fun uu____4569 ->
                                          match uu____4569 with
                                          | (bv, uu____4581) ->
                                              (non_dependent_or_raise s
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s))
                                     FStar_Syntax_Syntax.no_names binders1 in
                                 let ct = FStar_Syntax_Util.comp_result c1 in
                                 (non_dependent_or_raise s ct;
                                  (let k = n - (FStar_List.length binders1) in
                                   if k > Prims.int_zero
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found -> false)
            | uu____4601 ->
                ((let uu____4603 =
                    let uu____4608 =
                      let uu____4609 = FStar_Syntax_Print.term_to_string ty in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____4609 in
                    (FStar_Errors.Warning_NotDependentArrow, uu____4608) in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____4603);
                 false) in
          let rec is_valid_application head1 =
            let uu____4620 =
              let uu____4621 = FStar_Syntax_Subst.compress head1 in
              uu____4621.FStar_Syntax_Syntax.n in
            match uu____4620 with
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
                  (let uu____4626 = FStar_Syntax_Subst.compress head1 in
                   FStar_Syntax_Util.is_tuple_constructor uu____4626)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____4628 =
                  FStar_TypeChecker_Env.lookup_lid env1.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____4628 with
                 | ((uu____4637, ty), uu____4639) ->
                     let uu____4644 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____4644
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env1.tcenv
                           t1 in
                       let uu____4654 =
                         let uu____4655 = FStar_Syntax_Subst.compress res in
                         uu____4655.FStar_Syntax_Syntax.n in
                       (match uu____4654 with
                        | FStar_Syntax_Syntax.Tm_app uu____4658 -> true
                        | uu____4675 ->
                            ((let uu____4677 =
                                let uu____4682 =
                                  let uu____4683 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____4683 in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____4682) in
                              FStar_Errors.log_issue
                                head1.FStar_Syntax_Syntax.pos uu____4677);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____4685 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4686 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2, uu____4688) ->
                is_valid_application t2
            | uu____4693 -> false in
          let uu____4694 = is_valid_application head in
          if uu____4694
          then
            let uu____4695 =
              let uu____4696 =
                let uu____4713 =
                  FStar_List.map
                    (fun uu____4742 ->
                       match uu____4742 with
                       | (t2, qual) ->
                           let uu____4767 = star_type' env1 t2 in
                           (uu____4767, qual)) args in
                (head, uu____4713) in
              FStar_Syntax_Syntax.Tm_app uu____4696 in
            mk uu____4695
          else
            (let uu____4783 =
               let uu____4788 =
                 let uu____4789 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____4789 in
               (FStar_Errors.Fatal_WrongTerm, uu____4788) in
             FStar_Errors.raise_err uu____4783)
      | FStar_Syntax_Syntax.Tm_bvar uu____4790 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____4791 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____4792 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____4793 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders, repr, something) ->
          let uu____4821 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____4821 with
           | (binders1, repr1) ->
               let env2 =
                 let uu___520_4829 = env1 in
                 let uu____4830 =
                   FStar_TypeChecker_Env.push_binders env1.tcenv binders1 in
                 {
                   tcenv = uu____4830;
                   subst = (uu___520_4829.subst);
                   tc_const = (uu___520_4829.tc_const)
                 } in
               let repr2 = star_type' env2 repr1 in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x, t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x in
          let sort = star_type' env1 x1.FStar_Syntax_Syntax.sort in
          let subst = [FStar_Syntax_Syntax.DB (Prims.int_zero, x1)] in
          let t3 = FStar_Syntax_Subst.subst subst t2 in
          let t4 = star_type' env1 t3 in
          let subst1 = [FStar_Syntax_Syntax.NM (x1, Prims.int_zero)] in
          let t5 = FStar_Syntax_Subst.subst subst1 t4 in
          mk
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___535_4852 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___535_4852.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___535_4852.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2, m) ->
          let uu____4859 =
            let uu____4860 =
              let uu____4867 = star_type' env1 t2 in (uu____4867, m) in
            FStar_Syntax_Syntax.Tm_meta uu____4860 in
          mk uu____4859
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Util.Inl t2, FStar_Pervasives_Native.None), something)
          ->
          let uu____4919 =
            let uu____4920 =
              let uu____4947 = star_type' env1 e in
              let uu____4950 =
                let uu____4967 =
                  let uu____4976 = star_type' env1 t2 in
                  FStar_Util.Inl uu____4976 in
                (uu____4967, FStar_Pervasives_Native.None) in
              (uu____4947, uu____4950, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____4920 in
          mk uu____4919
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Util.Inr c, FStar_Pervasives_Native.None), something) ->
          let uu____5064 =
            let uu____5065 =
              let uu____5092 = star_type' env1 e in
              let uu____5095 =
                let uu____5112 =
                  let uu____5121 =
                    star_type' env1 (FStar_Syntax_Util.comp_result c) in
                  FStar_Util.Inl uu____5121 in
                (uu____5112, FStar_Pervasives_Native.None) in
              (uu____5092, uu____5095, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____5065 in
          mk uu____5064
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____5162, (uu____5163, FStar_Pervasives_Native.Some uu____5164),
           uu____5165)
          ->
          let uu____5214 =
            let uu____5219 =
              let uu____5220 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____5220 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5219) in
          FStar_Errors.raise_err uu____5214
      | FStar_Syntax_Syntax.Tm_refine uu____5221 ->
          let uu____5228 =
            let uu____5233 =
              let uu____5234 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____5234 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5233) in
          FStar_Errors.raise_err uu____5228
      | FStar_Syntax_Syntax.Tm_uinst uu____5235 ->
          let uu____5242 =
            let uu____5247 =
              let uu____5248 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____5248 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5247) in
          FStar_Errors.raise_err uu____5242
      | FStar_Syntax_Syntax.Tm_quoted uu____5249 ->
          let uu____5256 =
            let uu____5261 =
              let uu____5262 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____5262 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5261) in
          FStar_Errors.raise_err uu____5256
      | FStar_Syntax_Syntax.Tm_constant uu____5263 ->
          let uu____5264 =
            let uu____5269 =
              let uu____5270 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____5270 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5269) in
          FStar_Errors.raise_err uu____5264
      | FStar_Syntax_Syntax.Tm_match uu____5271 ->
          let uu____5294 =
            let uu____5299 =
              let uu____5300 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____5300 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5299) in
          FStar_Errors.raise_err uu____5294
      | FStar_Syntax_Syntax.Tm_let uu____5301 ->
          let uu____5314 =
            let uu____5319 =
              let uu____5320 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____5320 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5319) in
          FStar_Errors.raise_err uu____5314
      | FStar_Syntax_Syntax.Tm_uvar uu____5321 ->
          let uu____5334 =
            let uu____5339 =
              let uu____5340 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____5340 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5339) in
          FStar_Errors.raise_err uu____5334
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____5341 =
            let uu____5346 =
              let uu____5347 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____5347 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____5346) in
          FStar_Errors.raise_err uu____5341
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5349 = FStar_Syntax_Util.unfold_lazy i in
          star_type' env1 uu____5349
      | FStar_Syntax_Syntax.Tm_delayed uu____5352 -> failwith "impossible"
let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_5373 ->
    match uu___3_5373 with
    | FStar_Pervasives_Native.None -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_5380 ->
                match uu___2_5380 with
                | FStar_Syntax_Syntax.CPS -> true
                | uu____5381 -> false))
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    let uu____5387 =
      let uu____5388 = FStar_Syntax_Subst.compress t in
      uu____5388.FStar_Syntax_Syntax.n in
    match uu____5387 with
    | FStar_Syntax_Syntax.Tm_app (head, args) when
        FStar_Syntax_Util.is_tuple_constructor head ->
        let r =
          let uu____5418 =
            let uu____5419 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____5419 in
          is_C uu____5418 in
        if r
        then
          ((let uu____5441 =
              let uu____5442 =
                FStar_List.for_all
                  (fun uu____5452 ->
                     match uu____5452 with | (h, uu____5460) -> is_C h) args in
              Prims.op_Negation uu____5442 in
            if uu____5441
            then
              let uu____5465 =
                let uu____5470 =
                  let uu____5471 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not a C-type (A * C): %s" uu____5471 in
                (FStar_Errors.Error_UnexpectedDM4FType, uu____5470) in
              FStar_Errors.raise_error uu____5465 t.FStar_Syntax_Syntax.pos
            else ());
           true)
        else
          ((let uu____5475 =
              let uu____5476 =
                FStar_List.for_all
                  (fun uu____5487 ->
                     match uu____5487 with
                     | (h, uu____5495) ->
                         let uu____5500 = is_C h in
                         Prims.op_Negation uu____5500) args in
              Prims.op_Negation uu____5476 in
            if uu____5475
            then
              let uu____5501 =
                let uu____5506 =
                  let uu____5507 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not a C-type (C * A): %s" uu____5507 in
                (FStar_Errors.Error_UnexpectedDM4FType, uu____5506) in
              FStar_Errors.raise_error uu____5501 t.FStar_Syntax_Syntax.pos
            else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
        let uu____5531 = nm_of_comp comp in
        (match uu____5531 with
         | M t1 ->
             ((let uu____5534 = is_C t1 in
               if uu____5534
               then
                 let uu____5535 =
                   let uu____5540 =
                     let uu____5541 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not a C-type (C -> C): %s"
                       uu____5541 in
                   (FStar_Errors.Error_UnexpectedDM4FType, uu____5540) in
                 FStar_Errors.raise_error uu____5535
                   t1.FStar_Syntax_Syntax.pos
               else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____5545) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu____5551) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____5557, uu____5558) -> is_C t1
    | uu____5599 -> false
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env1 ->
    fun t ->
      fun e ->
        let mk x = FStar_Syntax_Syntax.mk x e.FStar_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk env1 t in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type in
        let body =
          let uu____5632 =
            let uu____5633 =
              let uu____5650 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____5653 =
                let uu____5664 =
                  let uu____5673 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____5673) in
                [uu____5664] in
              (uu____5650, uu____5653) in
            FStar_Syntax_Syntax.Tm_app uu____5633 in
          mk uu____5632 in
        let uu____5708 =
          let uu____5709 = FStar_Syntax_Syntax.mk_binder p in [uu____5709] in
        FStar_Syntax_Util.abs uu____5708 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_5732 ->
    match uu___4_5732 with
    | FStar_Syntax_Syntax.Tm_unknown -> true
    | uu____5733 -> false
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      fun context_nm ->
        let return_if uu____5968 =
          match uu____5968 with
          | (rec_nm, s_e, u_e) ->
              let check1 t1 t2 =
                let uu____6005 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____6007 =
                       let uu____6008 =
                         FStar_TypeChecker_Rel.teq env1.tcenv t1 t2 in
                       FStar_TypeChecker_Env.is_trivial uu____6008 in
                     Prims.op_Negation uu____6007) in
                if uu____6005
                then
                  let uu____6009 =
                    let uu____6014 =
                      let uu____6015 = FStar_Syntax_Print.term_to_string e in
                      let uu____6016 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____6017 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____6015 uu____6016 uu____6017 in
                    (FStar_Errors.Fatal_TypeMismatch, uu____6014) in
                  FStar_Errors.raise_err uu____6009
                else () in
              (match (rec_nm, context_nm) with
               | (N t1, N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1, M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1, M t2) ->
                   (check1 t1 t2;
                    (let uu____6038 = mk_return env1 t1 s_e in
                     ((M t1), uu____6038, u_e)))
               | (M t1, N t2) ->
                   let uu____6045 =
                     let uu____6050 =
                       let uu____6051 = FStar_Syntax_Print.term_to_string e in
                       let uu____6052 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____6053 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____6051 uu____6052 uu____6053 in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____6050) in
                   FStar_Errors.raise_err uu____6045) in
        let ensure_m env2 e2 =
          let strip_m uu___5_6102 =
            match uu___5_6102 with
            | (M t, s_e, u_e) -> (t, s_e, u_e)
            | uu____6118 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____6138 =
                let uu____6143 =
                  let uu____6144 = FStar_Syntax_Print.term_to_string t in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____6144 in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____6143) in
              FStar_Errors.raise_error uu____6138 e2.FStar_Syntax_Syntax.pos
          | M uu____6151 ->
              let uu____6152 = check env2 e2 context_nm in strip_m uu____6152 in
        let uu____6159 =
          let uu____6160 = FStar_Syntax_Subst.compress e in
          uu____6160.FStar_Syntax_Syntax.n in
        match uu____6159 with
        | FStar_Syntax_Syntax.Tm_bvar uu____6169 ->
            let uu____6170 = infer env1 e in return_if uu____6170
        | FStar_Syntax_Syntax.Tm_name uu____6177 ->
            let uu____6178 = infer env1 e in return_if uu____6178
        | FStar_Syntax_Syntax.Tm_fvar uu____6185 ->
            let uu____6186 = infer env1 e in return_if uu____6186
        | FStar_Syntax_Syntax.Tm_abs uu____6193 ->
            let uu____6212 = infer env1 e in return_if uu____6212
        | FStar_Syntax_Syntax.Tm_constant uu____6219 ->
            let uu____6220 = infer env1 e in return_if uu____6220
        | FStar_Syntax_Syntax.Tm_quoted uu____6227 ->
            let uu____6234 = infer env1 e in return_if uu____6234
        | FStar_Syntax_Syntax.Tm_app uu____6241 ->
            let uu____6258 = infer env1 e in return_if uu____6258
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____6266 = FStar_Syntax_Util.unfold_lazy i in
            check env1 uu____6266 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
            mk_let env1 binding e2
              (fun env2 -> fun e21 -> check env2 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0, branches) ->
            mk_match env1 e0 branches
              (fun env2 -> fun body -> check env2 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1, uu____6328) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1, uu____6334) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1, uu____6340, uu____6341) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____6382 ->
            let uu____6395 =
              let uu____6396 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____6396 in
            failwith uu____6395
        | FStar_Syntax_Syntax.Tm_type uu____6403 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____6410 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____6431 ->
            let uu____6438 =
              let uu____6439 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____6439 in
            failwith uu____6438
        | FStar_Syntax_Syntax.Tm_uvar uu____6446 ->
            let uu____6459 =
              let uu____6460 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____6460 in
            failwith uu____6459
        | FStar_Syntax_Syntax.Tm_delayed uu____6467 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____6488 =
              let uu____6489 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____6489 in
            failwith uu____6488
and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mk x = FStar_Syntax_Syntax.mk x e.FStar_Syntax_Syntax.pos in
      let normalize =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env1.tcenv in
      let uu____6517 =
        let uu____6518 = FStar_Syntax_Subst.compress e in
        uu____6518.FStar_Syntax_Syntax.n in
      match uu____6517 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6536 = FStar_Syntax_Util.unfold_lazy i in
          infer env1 uu____6536
      | FStar_Syntax_Syntax.Tm_abs (binders, body, rc_opt) ->
          let subst_rc_opt subst rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____6587;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None;
                  FStar_Syntax_Syntax.residual_flags = uu____6588;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____6594 =
                  let uu___770_6595 = rc in
                  let uu____6596 =
                    let uu____6601 =
                      let uu____6604 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst uu____6604 in
                    FStar_Pervasives_Native.Some uu____6601 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___770_6595.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____6596;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___770_6595.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____6594 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst body in
          let rc_opt1 = subst_rc_opt subst rc_opt in
          let env2 =
            let uu___776_6616 = env1 in
            let uu____6617 =
              FStar_TypeChecker_Env.push_binders env1.tcenv binders1 in
            {
              tcenv = uu____6617;
              subst = (uu___776_6616.subst);
              tc_const = (uu___776_6616.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____6643 ->
                 match uu____6643 with
                 | (bv, qual) ->
                     let sort = star_type' env2 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___783_6666 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___783_6666.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___783_6666.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____6667 =
            FStar_List.fold_left
              (fun uu____6698 ->
                 fun uu____6699 ->
                   match (uu____6698, uu____6699) with
                   | ((env3, acc), (bv, qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____6757 = is_C c in
                       if uu____6757
                       then
                         let xw =
                           let uu____6765 =
                             let uu____6766 =
                               FStar_Ident.string_of_id
                                 bv.FStar_Syntax_Syntax.ppname in
                             Prims.op_Hat uu____6766 "__w" in
                           let uu____6767 = star_type' env3 c in
                           FStar_Syntax_Syntax.gen_bv uu____6765
                             FStar_Pervasives_Native.None uu____6767 in
                         let x =
                           let uu___795_6769 = bv in
                           let uu____6770 =
                             let uu____6773 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env3 c uu____6773 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___795_6769.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___795_6769.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____6770
                           } in
                         let env4 =
                           let uu___798_6775 = env3 in
                           let uu____6776 =
                             let uu____6779 =
                               let uu____6780 =
                                 let uu____6787 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____6787) in
                               FStar_Syntax_Syntax.NT uu____6780 in
                             uu____6779 :: (env3.subst) in
                           {
                             tcenv = (uu___798_6775.tcenv);
                             subst = uu____6776;
                             tc_const = (uu___798_6775.tc_const)
                           } in
                         let uu____6792 =
                           let uu____6795 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____6796 =
                             let uu____6799 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____6799 :: acc in
                           uu____6795 :: uu____6796 in
                         (env4, uu____6792)
                       else
                         (let x =
                            let uu___801_6804 = bv in
                            let uu____6805 =
                              star_type' env3 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___801_6804.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___801_6804.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____6805
                            } in
                          let uu____6808 =
                            let uu____6811 = FStar_Syntax_Syntax.mk_binder x in
                            uu____6811 :: acc in
                          (env3, uu____6808))) (env2, []) binders1 in
          (match uu____6667 with
           | (env3, u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____6831 =
                 let check_what =
                   let uu____6857 = is_monadic rc_opt1 in
                   if uu____6857 then check_m else check_n in
                 let uu____6871 = check_what env3 body1 in
                 match uu____6871 with
                 | (t, s_body, u_body) ->
                     let uu____6891 =
                       let uu____6894 =
                         let uu____6895 = is_monadic rc_opt1 in
                         if uu____6895 then M t else N t in
                       comp_of_nm uu____6894 in
                     (uu____6891, s_body, u_body) in
               (match uu____6831 with
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
                                 let uu____6932 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_6936 ->
                                           match uu___6_6936 with
                                           | FStar_Syntax_Syntax.CPS -> true
                                           | uu____6937 -> false)) in
                                 if uu____6932
                                 then
                                   let uu____6938 =
                                     FStar_List.filter
                                       (fun uu___7_6942 ->
                                          match uu___7_6942 with
                                          | FStar_Syntax_Syntax.CPS -> false
                                          | uu____6943 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____6938
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____6952 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_6956 ->
                                         match uu___8_6956 with
                                         | FStar_Syntax_Syntax.CPS -> true
                                         | uu____6957 -> false)) in
                               if uu____6952
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_6964 ->
                                        match uu___9_6964 with
                                        | FStar_Syntax_Syntax.CPS -> false
                                        | uu____6965 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____6966 =
                                   let uu____6967 =
                                     let uu____6972 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____6972 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____6967 flags in
                                 FStar_Pervasives_Native.Some uu____6966
                               else
                                 (let uu____6978 =
                                    let uu___842_6979 = rc in
                                    let uu____6980 =
                                      let uu____6985 = star_type' env3 rt in
                                      FStar_Pervasives_Native.Some uu____6985 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___842_6979.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____6980;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___842_6979.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____6978)) in
                    let uu____6990 =
                      let comp1 =
                        let uu____6998 = is_monadic rc_opt1 in
                        let uu____6999 =
                          FStar_Syntax_Subst.subst env3.subst s_body in
                        trans_G env3 (FStar_Syntax_Util.comp_result comp)
                          uu____6998 uu____6999 in
                      let uu____7000 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____7000,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____6990 with
                     | (u_body1, u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____7038 =
                             let uu____7039 =
                               let uu____7058 =
                                 let uu____7061 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____7061 s_rc_opt in
                               (s_binders1, s_body1, uu____7058) in
                             FStar_Syntax_Syntax.Tm_abs uu____7039 in
                           mk uu____7038 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____7081 =
                             let uu____7082 =
                               let uu____7101 =
                                 let uu____7104 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____7104 u_rc_opt in
                               (u_binders2, u_body2, uu____7101) in
                             FStar_Syntax_Syntax.Tm_abs uu____7082 in
                           mk uu____7081 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____7120;_};
            FStar_Syntax_Syntax.fv_delta = uu____7121;
            FStar_Syntax_Syntax.fv_qual = uu____7122;_}
          ->
          let uu____7125 =
            let uu____7130 = FStar_TypeChecker_Env.lookup_lid env1.tcenv lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____7130 in
          (match uu____7125 with
           | (uu____7161, t) ->
               let uu____7163 = let uu____7164 = normalize t in N uu____7164 in
               (uu____7163, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____7165;
             FStar_Syntax_Syntax.vars = uu____7166;_},
           a::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____7245 = FStar_Syntax_Util.head_and_args e in
          (match uu____7245 with
           | (unary_op, uu____7269) ->
               let head = mk (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk (FStar_Syntax_Syntax.Tm_app (head, rest1)) in
               infer env1 t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____7340;
             FStar_Syntax_Syntax.vars = uu____7341;_},
           a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu____7437 = FStar_Syntax_Util.head_and_args e in
          (match uu____7437 with
           | (unary_op, uu____7461) ->
               let head =
                 mk (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk (FStar_Syntax_Syntax.Tm_app (head, rest1)) in
               infer env1 t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____7540;
             FStar_Syntax_Syntax.vars = uu____7541;_},
           (a, FStar_Pervasives_Native.None)::[])
          ->
          let uu____7579 = infer env1 a in
          (match uu____7579 with
           | (t, s, u) ->
               let uu____7595 = FStar_Syntax_Util.head_and_args e in
               (match uu____7595 with
                | (head, uu____7619) ->
                    let uu____7644 =
                      let uu____7645 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____7645 in
                    let uu____7646 =
                      let uu____7647 =
                        let uu____7648 =
                          let uu____7665 =
                            let uu____7676 = FStar_Syntax_Syntax.as_arg s in
                            [uu____7676] in
                          (head, uu____7665) in
                        FStar_Syntax_Syntax.Tm_app uu____7648 in
                      mk uu____7647 in
                    let uu____7713 =
                      let uu____7714 =
                        let uu____7715 =
                          let uu____7732 =
                            let uu____7743 = FStar_Syntax_Syntax.as_arg u in
                            [uu____7743] in
                          (head, uu____7732) in
                        FStar_Syntax_Syntax.Tm_app uu____7715 in
                      mk uu____7714 in
                    (uu____7644, uu____7646, uu____7713)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____7780;
             FStar_Syntax_Syntax.vars = uu____7781;_},
           (a1, uu____7783)::a2::[])
          ->
          let uu____7839 = infer env1 a1 in
          (match uu____7839 with
           | (t, s, u) ->
               let uu____7855 = FStar_Syntax_Util.head_and_args e in
               (match uu____7855 with
                | (head, uu____7879) ->
                    let uu____7904 =
                      let uu____7905 =
                        let uu____7906 =
                          let uu____7923 =
                            let uu____7934 = FStar_Syntax_Syntax.as_arg s in
                            [uu____7934; a2] in
                          (head, uu____7923) in
                        FStar_Syntax_Syntax.Tm_app uu____7906 in
                      mk uu____7905 in
                    let uu____7979 =
                      let uu____7980 =
                        let uu____7981 =
                          let uu____7998 =
                            let uu____8009 = FStar_Syntax_Syntax.as_arg u in
                            [uu____8009; a2] in
                          (head, uu____7998) in
                        FStar_Syntax_Syntax.Tm_app uu____7981 in
                      mk uu____7980 in
                    (t, uu____7904, uu____7979)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____8054;
             FStar_Syntax_Syntax.vars = uu____8055;_},
           uu____8056)
          ->
          let uu____8081 =
            let uu____8086 =
              let uu____8087 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8087 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8086) in
          FStar_Errors.raise_error uu____8081 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____8094;
             FStar_Syntax_Syntax.vars = uu____8095;_},
           uu____8096)
          ->
          let uu____8121 =
            let uu____8126 =
              let uu____8127 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____8127 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____8126) in
          FStar_Errors.raise_error uu____8121 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head, args) ->
          let uu____8160 = check_n env1 head in
          (match uu____8160 with
           | (t_head, s_head, u_head) ->
               let is_arrow t =
                 let uu____8182 =
                   let uu____8183 = FStar_Syntax_Subst.compress t in
                   uu____8183.FStar_Syntax_Syntax.n in
                 match uu____8182 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____8186 -> true
                 | uu____8201 -> false in
               let rec flatten t =
                 let uu____8222 =
                   let uu____8223 = FStar_Syntax_Subst.compress t in
                   uu____8223.FStar_Syntax_Syntax.n in
                 match uu____8222 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,
                      {
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                          (t1, uu____8242);
                        FStar_Syntax_Syntax.pos = uu____8243;
                        FStar_Syntax_Syntax.vars = uu____8244;_})
                     when is_arrow t1 ->
                     let uu____8273 = flatten t1 in
                     (match uu____8273 with
                      | (binders', comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1, uu____8373, uu____8374) -> flatten e1
                 | uu____8415 ->
                     let uu____8416 =
                       let uu____8421 =
                         let uu____8422 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____8422 in
                       (FStar_Errors.Fatal_NotFunctionType, uu____8421) in
                     FStar_Errors.raise_err uu____8416 in
               let uu____8437 = flatten t_head in
               (match uu____8437 with
                | (binders, comp) ->
                    let n = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____8511 =
                          let uu____8516 =
                            let uu____8517 = FStar_Util.string_of_int n in
                            let uu____8518 =
                              FStar_Util.string_of_int (n' - n) in
                            let uu____8519 = FStar_Util.string_of_int n in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____8517 uu____8518 uu____8519 in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____8516) in
                        FStar_Errors.raise_err uu____8511)
                     else ();
                     (let uu____8521 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____8521 with
                      | (binders1, comp1) ->
                          let rec final_type subst uu____8574 args1 =
                            match uu____8574 with
                            | (binders2, comp2) ->
                                (match (binders2, args1) with
                                 | ([], []) ->
                                     let uu____8674 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         comp2 in
                                     nm_of_comp uu____8674
                                 | (binders3, []) ->
                                     let uu____8712 =
                                       let uu____8713 =
                                         let uu____8716 =
                                           let uu____8717 =
                                             mk
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst
                                             uu____8717 in
                                         FStar_Syntax_Subst.compress
                                           uu____8716 in
                                       uu____8713.FStar_Syntax_Syntax.n in
                                     (match uu____8712 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4, comp3) ->
                                          let uu____8750 =
                                            let uu____8751 =
                                              let uu____8752 =
                                                let uu____8767 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____8767) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____8752 in
                                            mk uu____8751 in
                                          N uu____8750
                                      | uu____8780 -> failwith "wat?")
                                 | ([], uu____8781::uu____8782) ->
                                     failwith "just checked that?!"
                                 | ((bv, uu____8834)::binders3,
                                    (arg, uu____8837)::args2) ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____8924 = FStar_List.splitAt n' binders1 in
                          (match uu____8924 with
                           | (binders2, uu____8958) ->
                               let uu____8991 =
                                 let uu____9014 =
                                   FStar_List.map2
                                     (fun uu____9076 ->
                                        fun uu____9077 ->
                                          match (uu____9076, uu____9077) with
                                          | ((bv, uu____9125), (arg, q)) ->
                                              let uu____9154 =
                                                let uu____9155 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____9155.FStar_Syntax_Syntax.n in
                                              (match uu____9154 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____9176 ->
                                                   let uu____9177 =
                                                     let uu____9184 =
                                                       star_type' env1 arg in
                                                     (uu____9184, q) in
                                                   (uu____9177, [(arg, q)])
                                               | uu____9221 ->
                                                   let uu____9222 =
                                                     check_n env1 arg in
                                                   (match uu____9222 with
                                                    | (uu____9247, s_arg,
                                                       u_arg) ->
                                                        let uu____9250 =
                                                          let uu____9259 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____9259
                                                          then
                                                            let uu____9268 =
                                                              let uu____9275
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env1.subst
                                                                  s_arg in
                                                              (uu____9275, q) in
                                                            [uu____9268;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____9250))))
                                     binders2 args in
                                 FStar_List.split uu____9014 in
                               (match uu____8991 with
                                | (s_args, u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____9402 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____9415 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____9402, uu____9415)))))))
      | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
          mk_let env1 binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0, branches) ->
          mk_match env1 e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1, uu____9481) -> infer env1 e1
      | FStar_Syntax_Syntax.Tm_meta (e1, uu____9487) -> infer env1 e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1, uu____9493, uu____9494) ->
          infer env1 e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____9536 = let uu____9537 = env1.tc_const c in N uu____9537 in
          (uu____9536, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm, qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____9544 ->
          let uu____9557 =
            let uu____9558 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____9558 in
          failwith uu____9557
      | FStar_Syntax_Syntax.Tm_type uu____9565 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____9572 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____9593 ->
          let uu____9600 =
            let uu____9601 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____9601 in
          failwith uu____9600
      | FStar_Syntax_Syntax.Tm_uvar uu____9608 ->
          let uu____9621 =
            let uu____9622 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____9622 in
          failwith uu____9621
      | FStar_Syntax_Syntax.Tm_delayed uu____9629 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____9650 =
            let uu____9651 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____9651 in
          failwith uu____9650
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
  fun env1 ->
    fun e0 ->
      fun branches ->
        fun f ->
          let mk x = FStar_Syntax_Syntax.mk x e0.FStar_Syntax_Syntax.pos in
          let uu____9698 = check_n env1 e0 in
          match uu____9698 with
          | (uu____9711, s_e0, u_e0) ->
              let uu____9714 =
                let uu____9743 =
                  FStar_List.map
                    (fun b ->
                       let uu____9804 = FStar_Syntax_Subst.open_branch b in
                       match uu____9804 with
                       | (pat, FStar_Pervasives_Native.None, body) ->
                           let env2 =
                             let uu___1117_9846 = env1 in
                             let uu____9847 =
                               let uu____9848 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env1.tcenv
                                 uu____9848 in
                             {
                               tcenv = uu____9847;
                               subst = (uu___1117_9846.subst);
                               tc_const = (uu___1117_9846.tc_const)
                             } in
                           let uu____9851 = f env2 body in
                           (match uu____9851 with
                            | (nm1, s_body, u_body) ->
                                (nm1,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____9923 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____9743 in
              (match uu____9714 with
               | (nms, branches1) ->
                   let t1 =
                     let uu____10027 = FStar_List.hd nms in
                     match uu____10027 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_10035 ->
                          match uu___10_10035 with
                          | M uu____10036 -> true
                          | uu____10037 -> false) nms in
                   let uu____10038 =
                     let uu____10075 =
                       FStar_List.map2
                         (fun nm1 ->
                            fun uu____10165 ->
                              match uu____10165 with
                              | (pat, guard, (s_body, u_body, original_body))
                                  ->
                                  (match (nm1, has_m) with
                                   | (N t2, false) ->
                                       (nm1, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2, true) ->
                                       (nm1, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2, true) ->
                                       let uu____10342 =
                                         check env1 original_body (M t2) in
                                       (match uu____10342 with
                                        | (uu____10379, s_body1, u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____10418, false) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____10075 in
                   (match uu____10038 with
                    | (nms1, s_branches, u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk env1 t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____10602 ->
                                 match uu____10602 with
                                 | (pat, guard, s_body) ->
                                     let s_body1 =
                                       let uu____10653 =
                                         let uu____10654 =
                                           let uu____10671 =
                                             let uu____10682 =
                                               let uu____10691 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____10694 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____10691, uu____10694) in
                                             [uu____10682] in
                                           (s_body, uu____10671) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____10654 in
                                       mk uu____10653 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____10828 =
                              let uu____10829 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____10829] in
                            let uu____10848 =
                              mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____10828 uu____10848
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____10872 =
                              let uu____10881 =
                                let uu____10888 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____10888 in
                              [uu____10881] in
                            let uu____10907 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____10872 uu____10907 in
                          let uu____10910 =
                            mk
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____10949 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____10910, uu____10949)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____11058 =
                             let uu____11059 =
                               let uu____11060 =
                                 let uu____11087 =
                                   mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____11087,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11060 in
                             mk uu____11059 in
                           let uu____11146 =
                             mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____11058, uu____11146))))
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
  fun env1 ->
    fun binding ->
      fun e2 ->
        fun proceed ->
          fun ensure_m ->
            let mk x = FStar_Syntax_Syntax.mk x e2.FStar_Syntax_Syntax.pos in
            let e1 = binding.FStar_Syntax_Syntax.lbdef in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname in
            let x_binders =
              let uu____11211 = FStar_Syntax_Syntax.mk_binder x in
              [uu____11211] in
            let uu____11230 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____11230 with
            | (x_binders1, e21) ->
                let uu____11243 = infer env1 e1 in
                (match uu____11243 with
                 | (N t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu____11260 = is_C t1 in
                       if uu____11260
                       then
                         let uu___1203_11261 = binding in
                         let uu____11262 =
                           let uu____11265 =
                             FStar_Syntax_Subst.subst env1.subst s_e1 in
                           trans_F_ env1 t1 uu____11265 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1203_11261.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1203_11261.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____11262;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1203_11261.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1203_11261.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1203_11261.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1203_11261.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding in
                     let env2 =
                       let uu___1206_11268 = env1 in
                       let uu____11269 =
                         FStar_TypeChecker_Env.push_bv env1.tcenv
                           (let uu___1208_11271 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1208_11271.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1208_11271.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         tcenv = uu____11269;
                         subst = (uu___1206_11268.subst);
                         tc_const = (uu___1206_11268.tc_const)
                       } in
                     let uu____11272 = proceed env2 e21 in
                     (match uu____11272 with
                      | (nm_rec, s_e2, u_e2) ->
                          let s_binding =
                            let uu___1215_11289 = binding in
                            let uu____11290 =
                              star_type' env2
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1215_11289.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1215_11289.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____11290;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1215_11289.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1215_11289.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1215_11289.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1215_11289.FStar_Syntax_Syntax.lbpos)
                            } in
                          let uu____11293 =
                            let uu____11294 =
                              let uu____11295 =
                                let uu____11308 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___1218_11322 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1218_11322.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1218_11322.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1218_11322.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1218_11322.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1218_11322.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1218_11322.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11308) in
                              FStar_Syntax_Syntax.Tm_let uu____11295 in
                            mk uu____11294 in
                          let uu____11323 =
                            let uu____11324 =
                              let uu____11325 =
                                let uu____11338 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___1220_11352 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1220_11352.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1220_11352.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1220_11352.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1220_11352.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1220_11352.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1220_11352.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11338) in
                              FStar_Syntax_Syntax.Tm_let uu____11325 in
                            mk uu____11324 in
                          (nm_rec, uu____11293, uu____11323))
                 | (M t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu___1227_11357 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1227_11357.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1227_11357.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1227_11357.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1227_11357.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1227_11357.FStar_Syntax_Syntax.lbpos)
                       } in
                     let env2 =
                       let uu___1230_11359 = env1 in
                       let uu____11360 =
                         FStar_TypeChecker_Env.push_bv env1.tcenv
                           (let uu___1232_11362 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1232_11362.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1232_11362.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         tcenv = uu____11360;
                         subst = (uu___1230_11359.subst);
                         tc_const = (uu___1230_11359.tc_const)
                       } in
                     let uu____11363 = ensure_m env2 e21 in
                     (match uu____11363 with
                      | (t2, s_e2, u_e2) ->
                          let p_type = mk_star_to_type mk env2 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____11386 =
                              let uu____11387 =
                                let uu____11404 =
                                  let uu____11415 =
                                    let uu____11424 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____11427 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____11424, uu____11427) in
                                  [uu____11415] in
                                (s_e2, uu____11404) in
                              FStar_Syntax_Syntax.Tm_app uu____11387 in
                            mk uu____11386 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____11468 =
                              let uu____11469 =
                                let uu____11486 =
                                  let uu____11497 =
                                    let uu____11506 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____11506) in
                                  [uu____11497] in
                                (s_e1, uu____11486) in
                              FStar_Syntax_Syntax.Tm_app uu____11469 in
                            mk uu____11468 in
                          let uu____11541 =
                            let uu____11542 =
                              let uu____11543 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____11543] in
                            FStar_Syntax_Util.abs uu____11542 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____11562 =
                            let uu____11563 =
                              let uu____11564 =
                                let uu____11577 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___1244_11591 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1244_11591.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1244_11591.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1244_11591.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1244_11591.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1244_11591.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1244_11591.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____11577) in
                              FStar_Syntax_Syntax.Tm_let uu____11564 in
                            mk uu____11563 in
                          ((M t2), uu____11541, uu____11562)))
and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mn =
        let uu____11601 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            e.FStar_Syntax_Syntax.pos in
        N uu____11601 in
      let uu____11602 = check env1 e mn in
      match uu____11602 with
      | (N t, s_e, u_e) -> (t, s_e, u_e)
      | uu____11618 -> failwith "[check_n]: impossible"
and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mn =
        let uu____11640 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            e.FStar_Syntax_Syntax.pos in
        M uu____11640 in
      let uu____11641 = check env1 e mn in
      match uu____11641 with
      | (M t, s_e, u_e) -> (t, s_e, u_e)
      | uu____11657 -> failwith "[check_m]: impossible"
and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm1 ->
    match nm1 with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t
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
  fun env1 ->
    fun c ->
      fun wp ->
        (let uu____11689 =
           let uu____11690 = is_C c in Prims.op_Negation uu____11690 in
         if uu____11689
         then
           let uu____11691 =
             let uu____11696 =
               let uu____11697 = FStar_Syntax_Print.term_to_string c in
               FStar_Util.format1 "Not a DM4F C-type: %s" uu____11697 in
             (FStar_Errors.Error_UnexpectedDM4FType, uu____11696) in
           FStar_Errors.raise_error uu____11691 c.FStar_Syntax_Syntax.pos
         else ());
        (let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos in
         let uu____11707 =
           let uu____11708 = FStar_Syntax_Subst.compress c in
           uu____11708.FStar_Syntax_Syntax.n in
         match uu____11707 with
         | FStar_Syntax_Syntax.Tm_app (head, args) ->
             let uu____11737 = FStar_Syntax_Util.head_and_args wp in
             (match uu____11737 with
              | (wp_head, wp_args) ->
                  ((let uu____11781 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____11799 =
                           let uu____11800 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____11800 in
                         Prims.op_Negation uu____11799) in
                    if uu____11781 then failwith "mismatch" else ());
                   (let uu____11810 =
                      let uu____11811 =
                        let uu____11828 =
                          FStar_List.map2
                            (fun uu____11866 ->
                               fun uu____11867 ->
                                 match (uu____11866, uu____11867) with
                                 | ((arg, q), (wp_arg, q')) ->
                                     let print_implicit q1 =
                                       let uu____11928 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____11928
                                       then "implicit"
                                       else "explicit" in
                                     ((let uu____11931 =
                                         let uu____11932 =
                                           FStar_Syntax_Util.eq_aqual q q' in
                                         uu____11932 <>
                                           FStar_Syntax_Util.Equal in
                                       if uu____11931
                                       then
                                         let uu____11933 =
                                           let uu____11938 =
                                             let uu____11939 =
                                               print_implicit q in
                                             let uu____11940 =
                                               print_implicit q' in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____11939 uu____11940 in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____11938) in
                                         FStar_Errors.log_issue
                                           head.FStar_Syntax_Syntax.pos
                                           uu____11933
                                       else ());
                                      (let uu____11942 =
                                         trans_F_ env1 arg wp_arg in
                                       (uu____11942, q)))) args wp_args in
                        (head, uu____11828) in
                      FStar_Syntax_Syntax.Tm_app uu____11811 in
                    mk uu____11810)))
         | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____11988 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____11988 with
              | (binders_orig, comp1) ->
                  let uu____11995 =
                    let uu____12012 =
                      FStar_List.map
                        (fun uu____12052 ->
                           match uu____12052 with
                           | (bv, q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____12080 = is_C h in
                               if uu____12080
                               then
                                 let w' =
                                   let uu____12094 =
                                     let uu____12095 =
                                       FStar_Ident.string_of_id
                                         bv.FStar_Syntax_Syntax.ppname in
                                     Prims.op_Hat uu____12095 "__w'" in
                                   let uu____12096 = star_type' env1 h in
                                   FStar_Syntax_Syntax.gen_bv uu____12094
                                     FStar_Pervasives_Native.None uu____12096 in
                                 let uu____12097 =
                                   let uu____12106 =
                                     let uu____12115 =
                                       let uu____12122 =
                                         let uu____12123 =
                                           let uu____12124 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env1 h uu____12124 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____12123 in
                                       (uu____12122, q) in
                                     [uu____12115] in
                                   (w', q) :: uu____12106 in
                                 (w', uu____12097)
                               else
                                 (let x =
                                    let uu____12157 =
                                      let uu____12158 =
                                        FStar_Ident.string_of_id
                                          bv.FStar_Syntax_Syntax.ppname in
                                      Prims.op_Hat uu____12158 "__x" in
                                    let uu____12159 = star_type' env1 h in
                                    FStar_Syntax_Syntax.gen_bv uu____12157
                                      FStar_Pervasives_Native.None
                                      uu____12159 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____12012 in
                  (match uu____11995 with
                   | (bvs, binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____12232 =
                           let uu____12235 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____12235 in
                         FStar_Syntax_Subst.subst_comp uu____12232 comp1 in
                       let app =
                         let uu____12239 =
                           let uu____12240 =
                             let uu____12257 =
                               FStar_List.map
                                 (fun bv ->
                                    let uu____12276 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____12277 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____12276, uu____12277)) bvs in
                             (wp, uu____12257) in
                           FStar_Syntax_Syntax.Tm_app uu____12240 in
                         mk uu____12239 in
                       let comp3 =
                         let uu____12291 = type_of_comp comp2 in
                         let uu____12292 = is_monadic_comp comp2 in
                         trans_G env1 uu____12291 uu____12292 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e, uu____12294, uu____12295) ->
             trans_F_ env1 e wp
         | uu____12336 -> failwith "impossible trans_F_")
and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env1 ->
    fun h ->
      fun is_monadic1 ->
        fun wp ->
          if is_monadic1
          then
            let uu____12341 =
              let uu____12342 = star_type' env1 h in
              let uu____12345 =
                let uu____12356 =
                  let uu____12365 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____12365) in
                [uu____12356] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____12342;
                FStar_Syntax_Syntax.effect_args = uu____12345;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____12341
          else
            (let uu____12389 = trans_F_ env1 h wp in
             FStar_Syntax_Syntax.mk_Total uu____12389)
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
  fun env1 ->
    fun t -> let uu____12408 = n env1.tcenv t in star_type' env1 uu____12408
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun t -> let uu____12427 = n env1.tcenv t in check_n env1 uu____12427
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun wp ->
        let uu____12443 = n env1.tcenv c in
        let uu____12444 = n env1.tcenv wp in
        trans_F_ env1 uu____12443 uu____12444
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun env1 ->
      fun t ->
        (let uu____12461 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
         if uu____12461
         then
           let uu____12462 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s
             uu____12462
         else ());
        (let uu____12464 = FStar_TypeChecker_TcTerm.tc_term env1 t in
         match uu____12464 with
         | (t', uu____12472, uu____12473) ->
             ((let uu____12475 =
                 FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
               if uu____12475
               then
                 let uu____12476 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu____12476
               else ());
              t'))
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env1 ->
    fun ed ->
      let uu____12508 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature) in
      match uu____12508 with
      | (effect_binders_un, signature_un) ->
          let uu____12529 =
            FStar_TypeChecker_TcTerm.tc_tparams env1 effect_binders_un in
          (match uu____12529 with
           | (effect_binders, env2, uu____12548) ->
               let uu____12549 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env2 signature_un in
               (match uu____12549 with
                | (signature, uu____12565) ->
                    let raise_error uu____12580 =
                      match uu____12580 with
                      | (e, err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos in
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____12612 ->
                           match uu____12612 with
                           | (bv, qual) ->
                               let uu____12631 =
                                 let uu___1370_12632 = bv in
                                 let uu____12633 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.EraseUniverses]
                                     env2 bv.FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1370_12632.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1370_12632.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____12633
                                 } in
                               (uu____12631, qual)) effect_binders in
                    let uu____12638 =
                      let uu____12645 =
                        let uu____12646 =
                          FStar_Syntax_Subst.compress signature_un in
                        uu____12646.FStar_Syntax_Syntax.n in
                      match uu____12645 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a, uu____12656)::[], effect_marker) ->
                          (a, effect_marker)
                      | uu____12688 ->
                          raise_error
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature") in
                    (match uu____12638 with
                     | (a, effect_marker) ->
                         let a1 =
                           let uu____12712 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu____12712
                           then
                             let uu____12713 =
                               let uu____12716 =
                                 FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu____12716 in
                             FStar_Syntax_Syntax.gen_bv "a" uu____12713
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env3 other_binders t =
                           let subst =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst t in
                           let uu____12762 =
                             FStar_TypeChecker_TcTerm.tc_term env3 t1 in
                           match uu____12762 with
                           | (t2, comp, uu____12775) -> (t2, comp) in
                         let mk x =
                           FStar_Syntax_Syntax.mk x
                             signature.FStar_Syntax_Syntax.pos in
                         let uu____12784 =
                           let uu____12789 =
                             let uu____12790 =
                               let uu____12799 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____12799
                                 FStar_Util.must in
                             FStar_All.pipe_right uu____12790
                               FStar_Pervasives_Native.snd in
                           open_and_check env2 [] uu____12789 in
                         (match uu____12784 with
                          | (repr, _comp) ->
                              ((let uu____12845 =
                                  FStar_TypeChecker_Env.debug env2
                                    (FStar_Options.Other "ED") in
                                if uu____12845
                                then
                                  let uu____12846 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____12846
                                else ());
                               (let ed_range =
                                  FStar_TypeChecker_Env.get_range env2 in
                                let dmff_env =
                                  empty env2
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env2 FStar_Range.dummyRange) in
                                let wp_type = star_type dmff_env repr in
                                let uu____12851 =
                                  recheck_debug "*" env2 wp_type in
                                let wp_a =
                                  let uu____12853 =
                                    let uu____12854 =
                                      let uu____12855 =
                                        let uu____12872 =
                                          let uu____12883 =
                                            let uu____12892 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu____12895 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu____12892, uu____12895) in
                                          [uu____12883] in
                                        (wp_type, uu____12872) in
                                      FStar_Syntax_Syntax.Tm_app uu____12855 in
                                    mk uu____12854 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env2
                                    uu____12853 in
                                let effect_signature =
                                  let binders =
                                    let uu____12942 =
                                      let uu____12949 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      (a1, uu____12949) in
                                    let uu____12954 =
                                      let uu____12963 =
                                        let uu____12970 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu____12970
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu____12963] in
                                    uu____12942 :: uu____12954 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let uu____13006 =
                                  recheck_debug
                                    "turned into the effect signature" env2
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env3 = get_env dmff_env1 in
                                  let uu____13069 = item in
                                  match uu____13069 with
                                  | (u_item, item1) ->
                                      let uu____13084 =
                                        open_and_check env3 other_binders
                                          item1 in
                                      (match uu____13084 with
                                       | (item2, item_comp) ->
                                           ((let uu____13100 =
                                               let uu____13101 =
                                                 FStar_TypeChecker_Common.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu____13101 in
                                             if uu____13100
                                             then
                                               let uu____13102 =
                                                 let uu____13107 =
                                                   let uu____13108 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu____13109 =
                                                     FStar_TypeChecker_Common.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____13108 uu____13109 in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu____13107) in
                                               FStar_Errors.raise_err
                                                 uu____13102
                                             else ());
                                            (let uu____13111 =
                                               star_expr dmff_env1 item2 in
                                             match uu____13111 with
                                             | (item_t, item_wp, item_elab)
                                                 ->
                                                 let uu____13129 =
                                                   recheck_debug "*" env3
                                                     item_wp in
                                                 let uu____13130 =
                                                   recheck_debug "_" env3
                                                     item_elab in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab)))) in
                                let uu____13131 =
                                  let uu____13140 =
                                    let uu____13145 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr in
                                    FStar_All.pipe_right uu____13145
                                      FStar_Util.must in
                                  elaborate_and_star dmff_env [] uu____13140 in
                                match uu____13131 with
                                | (dmff_env1, uu____13173, bind_wp,
                                   bind_elab) ->
                                    let uu____13176 =
                                      let uu____13185 =
                                        let uu____13190 =
                                          FStar_All.pipe_right ed
                                            FStar_Syntax_Util.get_return_repr in
                                        FStar_All.pipe_right uu____13190
                                          FStar_Util.must in
                                      elaborate_and_star dmff_env1 []
                                        uu____13185 in
                                    (match uu____13176 with
                                     | (dmff_env2, uu____13218, return_wp,
                                        return_elab) ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu____13227 =
                                             let uu____13228 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____13228.FStar_Syntax_Syntax.n in
                                           match uu____13227 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu____13286 =
                                                 let uu____13305 =
                                                   let uu____13310 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____13310 in
                                                 match uu____13305 with
                                                 | (b11::b21::[], body1) ->
                                                     (b11, b21, body1)
                                                 | uu____13392 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu____13286 with
                                                | (b11, b21, body1) ->
                                                    let env0 =
                                                      let uu____13445 =
                                                        get_env dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____13445
                                                        [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu____13468 =
                                                          let uu____13469 =
                                                            let uu____13486 =
                                                              let uu____13497
                                                                =
                                                                let uu____13506
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    FStar_Pervasives_Native.fst
                                                                    b11) in
                                                                let uu____13511
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____13506,
                                                                  uu____13511) in
                                                              [uu____13497] in
                                                            (wp_type,
                                                              uu____13486) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____13469 in
                                                        mk uu____13468 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu____13546 =
                                                      let uu____13555 =
                                                        let uu____13556 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____13556 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____13555 in
                                                    (match uu____13546 with
                                                     | (bs1, body2, what') ->
                                                         let fail uu____13579
                                                           =
                                                           let error_msg =
                                                             let uu____13581
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu____13582
                                                               =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.string_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu____13581
                                                               uu____13582 in
                                                           raise_error
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg) in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                               -> fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu____13587
                                                                   =
                                                                   let uu____13588
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                                   Prims.op_Negation
                                                                    uu____13588 in
                                                                 if
                                                                   uu____13587
                                                                 then fail ()
                                                                 else ());
                                                                (let uu____13590
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
                                                                    FStar_Syntax_Util.ktype0 in
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
                                                                    fail ()) in
                                                                 FStar_All.pipe_right
                                                                   uu____13590
                                                                   (fun
                                                                    uu____13607
                                                                    -> ()))));
                                                          (let wp =
                                                             let t2 =
                                                               (FStar_Pervasives_Native.fst
                                                                  b21).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               double_star t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type in
                                                           let body3 =
                                                             let uu____13616
                                                               =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp in
                                                             let uu____13617
                                                               =
                                                               let uu____13618
                                                                 =
                                                                 let uu____13627
                                                                   =
                                                                   FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                 (uu____13627,
                                                                   FStar_Pervasives_Native.None) in
                                                               [uu____13618] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu____13616
                                                               uu____13617
                                                               ed_range in
                                                           let uu____13662 =
                                                             let uu____13663
                                                               =
                                                               let uu____13672
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu____13672] in
                                                             b11 ::
                                                               uu____13663 in
                                                           let uu____13697 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu____13662
                                                             uu____13697
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu____13700 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let return_wp1 =
                                           let uu____13706 =
                                             let uu____13707 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu____13707.FStar_Syntax_Syntax.n in
                                           match uu____13706 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu____13765 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____13765
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu____13786 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let bind_wp1 =
                                           let uu____13792 =
                                             let uu____13793 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu____13793.FStar_Syntax_Syntax.n in
                                           match uu____13792 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders, body, what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_constant_at_level
                                                      Prims.int_one)
                                                   FStar_Pervasives_Native.None in
                                               let uu____13826 =
                                                 let uu____13827 =
                                                   let uu____13836 =
                                                     let uu____13843 =
                                                       mk
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r) in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____13843 in
                                                   [uu____13836] in
                                                 FStar_List.append
                                                   uu____13827 binders in
                                               FStar_Syntax_Util.abs
                                                 uu____13826 body what
                                           | uu____13862 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind") in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = Prims.int_zero
                                           then t
                                           else
                                             (let uu____13886 =
                                                let uu____13887 =
                                                  let uu____13888 =
                                                    let uu____13905 =
                                                      let uu____13916 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu____13916 in
                                                    (t, uu____13905) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____13888 in
                                                mk uu____13887 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____13886) in
                                         let rec apply_last f l =
                                           match l with
                                           | [] ->
                                               failwith
                                                 "impossible: empty path.."
                                           | a2::[] ->
                                               let uu____13960 = f a2 in
                                               [uu____13960]
                                           | x::xs ->
                                               let uu____13965 =
                                                 apply_last f xs in
                                               x :: uu____13965 in
                                         let register maybe_admit name item =
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last
                                               (fun s ->
                                                  Prims.op_Hat "__"
                                                    (Prims.op_Hat s
                                                       (Prims.op_Hat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               ed_range in
                                           let uu____13996 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env2 l' in
                                           match uu____13996 with
                                           | FStar_Pervasives_Native.Some
                                               (_us, _t) ->
                                               ((let uu____14026 =
                                                   FStar_Options.debug_any () in
                                                 if uu____14026
                                                 then
                                                   let uu____14027 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu____14027
                                                 else ());
                                                (let uu____14029 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu____14029))
                                           | FStar_Pervasives_Native.None ->
                                               let uu____14038 =
                                                 let uu____14043 =
                                                   mk_lid name in
                                                 let uu____14044 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env2 uu____14043
                                                   uu____14044 in
                                               (match uu____14038 with
                                                | (sigelt, fv) ->
                                                    let sigelt1 =
                                                      if maybe_admit
                                                      then
                                                        let uu___1544_14048 =
                                                          sigelt in
                                                        {
                                                          FStar_Syntax_Syntax.sigel
                                                            =
                                                            (uu___1544_14048.FStar_Syntax_Syntax.sigel);
                                                          FStar_Syntax_Syntax.sigrng
                                                            =
                                                            (uu___1544_14048.FStar_Syntax_Syntax.sigrng);
                                                          FStar_Syntax_Syntax.sigquals
                                                            =
                                                            (uu___1544_14048.FStar_Syntax_Syntax.sigquals);
                                                          FStar_Syntax_Syntax.sigmeta
                                                            =
                                                            (let uu___1546_14050
                                                               =
                                                               sigelt.FStar_Syntax_Syntax.sigmeta in
                                                             {
                                                               FStar_Syntax_Syntax.sigmeta_active
                                                                 =
                                                                 (uu___1546_14050.FStar_Syntax_Syntax.sigmeta_active);
                                                               FStar_Syntax_Syntax.sigmeta_fact_db_ids
                                                                 =
                                                                 (uu___1546_14050.FStar_Syntax_Syntax.sigmeta_fact_db_ids);
                                                               FStar_Syntax_Syntax.sigmeta_admit
                                                                 = true
                                                             });
                                                          FStar_Syntax_Syntax.sigattrs
                                                            =
                                                            (uu___1544_14048.FStar_Syntax_Syntax.sigattrs);
                                                          FStar_Syntax_Syntax.sigopts
                                                            =
                                                            (uu___1544_14048.FStar_Syntax_Syntax.sigopts)
                                                        }
                                                      else sigelt in
                                                    ((let uu____14053 =
                                                        let uu____14056 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt1 ::
                                                          uu____14056 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu____14053);
                                                     fv)) in
                                         let register_admit = register true in
                                         let register1 = register false in
                                         let lift_from_pure_wp1 =
                                           register1 "lift_from_pure"
                                             lift_from_pure_wp in
                                         let mk_sigelt se =
                                           let uu___1555_14108 =
                                             FStar_Syntax_Syntax.mk_sigelt se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (uu___1555_14108.FStar_Syntax_Syntax.sigel);
                                             FStar_Syntax_Syntax.sigrng =
                                               ed_range;
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___1555_14108.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___1555_14108.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___1555_14108.FStar_Syntax_Syntax.sigattrs);
                                             FStar_Syntax_Syntax.sigopts =
                                               (uu___1555_14108.FStar_Syntax_Syntax.sigopts)
                                           } in
                                         let return_wp2 =
                                           register1 "return_wp" return_wp1 in
                                         ((let uu____14111 =
                                             let uu____14114 =
                                               mk_sigelt
                                                 (FStar_Syntax_Syntax.Sig_pragma
                                                    (FStar_Syntax_Syntax.PushOptions
                                                       FStar_Pervasives_Native.None)) in
                                             let uu____14115 =
                                               FStar_ST.op_Bang sigelts in
                                             uu____14114 :: uu____14115 in
                                           FStar_ST.op_Colon_Equals sigelts
                                             uu____14111);
                                          (let return_elab1 =
                                             register_admit "return_elab"
                                               return_elab in
                                           (let uu____14140 =
                                              let uu____14143 =
                                                mk_sigelt
                                                  (FStar_Syntax_Syntax.Sig_pragma
                                                     FStar_Syntax_Syntax.PopOptions) in
                                              let uu____14144 =
                                                FStar_ST.op_Bang sigelts in
                                              uu____14143 :: uu____14144 in
                                            FStar_ST.op_Colon_Equals sigelts
                                              uu____14140);
                                           (let bind_wp2 =
                                              register1 "bind_wp" bind_wp1 in
                                            (let uu____14169 =
                                               let uu____14172 =
                                                 mk_sigelt
                                                   (FStar_Syntax_Syntax.Sig_pragma
                                                      (FStar_Syntax_Syntax.PushOptions
                                                         FStar_Pervasives_Native.None)) in
                                               let uu____14173 =
                                                 FStar_ST.op_Bang sigelts in
                                               uu____14172 :: uu____14173 in
                                             FStar_ST.op_Colon_Equals sigelts
                                               uu____14169);
                                            (let bind_elab1 =
                                               register_admit "bind_elab"
                                                 bind_elab in
                                             (let uu____14198 =
                                                let uu____14201 =
                                                  mk_sigelt
                                                    (FStar_Syntax_Syntax.Sig_pragma
                                                       FStar_Syntax_Syntax.PopOptions) in
                                                let uu____14202 =
                                                  FStar_ST.op_Bang sigelts in
                                                uu____14201 :: uu____14202 in
                                              FStar_ST.op_Colon_Equals
                                                sigelts uu____14198);
                                             (let uu____14225 =
                                                FStar_List.fold_left
                                                  (fun uu____14265 ->
                                                     fun action ->
                                                       match uu____14265 with
                                                       | (dmff_env3, actions)
                                                           ->
                                                           let params_un =
                                                             FStar_Syntax_Subst.open_binders
                                                               action.FStar_Syntax_Syntax.action_params in
                                                           let uu____14286 =
                                                             let uu____14293
                                                               =
                                                               get_env
                                                                 dmff_env3 in
                                                             FStar_TypeChecker_TcTerm.tc_tparams
                                                               uu____14293
                                                               params_un in
                                                           (match uu____14286
                                                            with
                                                            | (action_params,
                                                               env',
                                                               uu____14302)
                                                                ->
                                                                let action_params1
                                                                  =
                                                                  FStar_List.map
                                                                    (
                                                                    fun
                                                                    uu____14328
                                                                    ->
                                                                    match uu____14328
                                                                    with
                                                                    | 
                                                                    (bv,
                                                                    qual) ->
                                                                    let uu____14347
                                                                    =
                                                                    let uu___1577_14348
                                                                    = bv in
                                                                    let uu____14349
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___1577_14348.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___1577_14348.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    uu____14349
                                                                    } in
                                                                    (uu____14347,
                                                                    qual))
                                                                    action_params in
                                                                let dmff_env'
                                                                  =
                                                                  set_env
                                                                    dmff_env3
                                                                    env' in
                                                                let uu____14355
                                                                  =
                                                                  elaborate_and_star
                                                                    dmff_env'
                                                                    action_params1
                                                                    ((action.FStar_Syntax_Syntax.action_univs),
                                                                    (action.FStar_Syntax_Syntax.action_defn)) in
                                                                (match uu____14355
                                                                 with
                                                                 | (dmff_env4,
                                                                    action_t,
                                                                    action_wp,
                                                                    action_elab)
                                                                    ->
                                                                    let name
                                                                    =
                                                                    let uu____14375
                                                                    =
                                                                    FStar_Ident.ident_of_lid
                                                                    action.FStar_Syntax_Syntax.action_name in
                                                                    FStar_Ident.string_of_id
                                                                    uu____14375 in
                                                                    let action_typ_with_wp
                                                                    =
                                                                    trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                    let action_params2
                                                                    =
                                                                    FStar_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                    let action_elab1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                    let action_typ_with_wp1
                                                                    =
                                                                    FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                    let action_elab2
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None in
                                                                    let action_typ_with_wp2
                                                                    =
                                                                    match action_params2
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    action_typ_with_wp1
                                                                    | 
                                                                    uu____14394
                                                                    ->
                                                                    let uu____14395
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu____14395 in
                                                                    ((
                                                                    let uu____14399
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                    if
                                                                    uu____14399
                                                                    then
                                                                    let uu____14400
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu____14401
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu____14402
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu____14403
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu____14400
                                                                    uu____14401
                                                                    uu____14402
                                                                    uu____14403
                                                                    else ());
                                                                    (let action_elab3
                                                                    =
                                                                    register1
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                    let action_typ_with_wp3
                                                                    =
                                                                    register1
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                    let uu____14407
                                                                    =
                                                                    let uu____14410
                                                                    =
                                                                    let uu___1599_14411
                                                                    = action in
                                                                    let uu____14412
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu____14413
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1599_14411.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1599_14411.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___1599_14411.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____14412;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____14413
                                                                    } in
                                                                    uu____14410
                                                                    ::
                                                                    actions in
                                                                    (dmff_env4,
                                                                    uu____14407))))))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions in
                                              match uu____14225 with
                                              | (dmff_env3, actions) ->
                                                  let actions1 =
                                                    FStar_List.rev actions in
                                                  let repr1 =
                                                    let wp =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_a"
                                                        FStar_Pervasives_Native.None
                                                        wp_a in
                                                    let binders =
                                                      let uu____14456 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1 in
                                                      let uu____14463 =
                                                        let uu____14472 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp in
                                                        [uu____14472] in
                                                      uu____14456 ::
                                                        uu____14463 in
                                                    let uu____14497 =
                                                      let uu____14500 =
                                                        let uu____14501 =
                                                          let uu____14502 =
                                                            let uu____14519 =
                                                              let uu____14530
                                                                =
                                                                let uu____14539
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1 in
                                                                let uu____14542
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu____14539,
                                                                  uu____14542) in
                                                              [uu____14530] in
                                                            (repr,
                                                              uu____14519) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____14502 in
                                                        mk uu____14501 in
                                                      let uu____14577 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp in
                                                      trans_F dmff_env3
                                                        uu____14500
                                                        uu____14577 in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____14497
                                                      FStar_Pervasives_Native.None in
                                                  let uu____14578 =
                                                    recheck_debug "FC" env2
                                                      repr1 in
                                                  let repr2 =
                                                    register1 "repr" repr1 in
                                                  let uu____14580 =
                                                    let uu____14589 =
                                                      let uu____14590 =
                                                        let uu____14593 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____14593 in
                                                      uu____14590.FStar_Syntax_Syntax.n in
                                                    match uu____14589 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,
                                                         arrow, uu____14607)
                                                        ->
                                                        let uu____14644 =
                                                          let uu____14665 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow in
                                                          match uu____14665
                                                          with
                                                          | (b::bs, body) ->
                                                              (b, bs, body)
                                                          | uu____14733 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity" in
                                                        (match uu____14644
                                                         with
                                                         | (type_param1,
                                                            effect_param1,
                                                            arrow1) ->
                                                             let uu____14797
                                                               =
                                                               let uu____14798
                                                                 =
                                                                 let uu____14801
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow1 in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____14801 in
                                                               uu____14798.FStar_Syntax_Syntax.n in
                                                             (match uu____14797
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,
                                                                   c)
                                                                  ->
                                                                  let uu____14834
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c in
                                                                  (match uu____14834
                                                                   with
                                                                   | 
                                                                   (wp_binders1,
                                                                    c1) ->
                                                                    let uu____14849
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____14880
                                                                    ->
                                                                    match uu____14880
                                                                    with
                                                                    | 
                                                                    (bv,
                                                                    uu____14888)
                                                                    ->
                                                                    let uu____14893
                                                                    =
                                                                    let uu____14894
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu____14894
                                                                    (FStar_Util.set_mem
                                                                    (FStar_Pervasives_Native.fst
                                                                    type_param1)) in
                                                                    FStar_All.pipe_right
                                                                    uu____14893
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                    (match uu____14849
                                                                    with
                                                                    | 
                                                                    (pre_args,
                                                                    post_args)
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
                                                                    let uu____14982
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu____14982 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu____14989
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu____14999
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu____14999 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg) in
                                                                    let uu____15006
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu____15009
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (FStar_Pervasives_Native.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu____15006,
                                                                    uu____15009)))
                                                              | uu____15024
                                                                  ->
                                                                  let uu____15025
                                                                    =
                                                                    let uu____15030
                                                                    =
                                                                    let uu____15031
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1 in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____15031 in
                                                                    (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                    uu____15030) in
                                                                  raise_error
                                                                    uu____15025))
                                                    | uu____15040 ->
                                                        let uu____15041 =
                                                          let uu____15046 =
                                                            let uu____15047 =
                                                              FStar_Syntax_Print.term_to_string
                                                                wp_type in
                                                            FStar_Util.format1
                                                              "Impossible: pre/post abs %s"
                                                              uu____15047 in
                                                          (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                            uu____15046) in
                                                        raise_error
                                                          uu____15041 in
                                                  (match uu____14580 with
                                                   | (pre, post) ->
                                                       ((let uu____15077 =
                                                           register1 "pre"
                                                             pre in
                                                         ());
                                                        (let uu____15079 =
                                                           register1 "post"
                                                             post in
                                                         ());
                                                        (let uu____15081 =
                                                           register1 "wp"
                                                             wp_type in
                                                         ());
                                                        (let ed_combs =
                                                           match ed.FStar_Syntax_Syntax.combinators
                                                           with
                                                           | FStar_Syntax_Syntax.DM4F_eff
                                                               combs ->
                                                               let uu____15084
                                                                 =
                                                                 let uu___1657_15085
                                                                   = combs in
                                                                 let uu____15086
                                                                   =
                                                                   let uu____15087
                                                                    =
                                                                    apply_close
                                                                    return_wp2 in
                                                                   ([],
                                                                    uu____15087) in
                                                                 let uu____15094
                                                                   =
                                                                   let uu____15095
                                                                    =
                                                                    apply_close
                                                                    bind_wp2 in
                                                                   ([],
                                                                    uu____15095) in
                                                                 let uu____15102
                                                                   =
                                                                   let uu____15105
                                                                    =
                                                                    let uu____15106
                                                                    =
                                                                    apply_close
                                                                    repr2 in
                                                                    ([],
                                                                    uu____15106) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____15105 in
                                                                 let uu____15113
                                                                   =
                                                                   let uu____15116
                                                                    =
                                                                    let uu____15117
                                                                    =
                                                                    apply_close
                                                                    return_elab1 in
                                                                    ([],
                                                                    uu____15117) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____15116 in
                                                                 let uu____15124
                                                                   =
                                                                   let uu____15127
                                                                    =
                                                                    let uu____15128
                                                                    =
                                                                    apply_close
                                                                    bind_elab1 in
                                                                    ([],
                                                                    uu____15128) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____15127 in
                                                                 {
                                                                   FStar_Syntax_Syntax.ret_wp
                                                                    =
                                                                    uu____15086;
                                                                   FStar_Syntax_Syntax.bind_wp
                                                                    =
                                                                    uu____15094;
                                                                   FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    (uu___1657_15085.FStar_Syntax_Syntax.stronger);
                                                                   FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    (uu___1657_15085.FStar_Syntax_Syntax.if_then_else);
                                                                   FStar_Syntax_Syntax.ite_wp
                                                                    =
                                                                    (uu___1657_15085.FStar_Syntax_Syntax.ite_wp);
                                                                   FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    (uu___1657_15085.FStar_Syntax_Syntax.close_wp);
                                                                   FStar_Syntax_Syntax.trivial
                                                                    =
                                                                    (uu___1657_15085.FStar_Syntax_Syntax.trivial);
                                                                   FStar_Syntax_Syntax.repr
                                                                    =
                                                                    uu____15102;
                                                                   FStar_Syntax_Syntax.return_repr
                                                                    =
                                                                    uu____15113;
                                                                   FStar_Syntax_Syntax.bind_repr
                                                                    =
                                                                    uu____15124
                                                                 } in
                                                               FStar_Syntax_Syntax.DM4F_eff
                                                                 uu____15084
                                                           | uu____15135 ->
                                                               failwith
                                                                 "Impossible! For a DM4F effect combinators must be in DM4f_eff" in
                                                         let ed1 =
                                                           let uu___1661_15137
                                                             = ed in
                                                           let uu____15138 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1 in
                                                           let uu____15139 =
                                                             let uu____15140
                                                               =
                                                               FStar_Syntax_Subst.close
                                                                 effect_binders1
                                                                 effect_signature in
                                                             ([],
                                                               uu____15140) in
                                                           {
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___1661_15137.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___1661_15137.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___1661_15137.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____15138;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____15139;
                                                             FStar_Syntax_Syntax.combinators
                                                               = ed_combs;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1;
                                                             FStar_Syntax_Syntax.eff_attrs
                                                               =
                                                               (uu___1661_15137.FStar_Syntax_Syntax.eff_attrs)
                                                           } in
                                                         let uu____15147 =
                                                           gen_wps_for_free
                                                             env2
                                                             effect_binders1
                                                             a1 wp_a ed1 in
                                                         match uu____15147
                                                         with
                                                         | (sigelts', ed2) ->
                                                             ((let uu____15165
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env2
                                                                   (FStar_Options.Other
                                                                    "ED") in
                                                               if uu____15165
                                                               then
                                                                 let uu____15166
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2 in
                                                                 FStar_Util.print_string
                                                                   uu____15166
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
                                                                    let uu____15180
                                                                    =
                                                                    let uu____15183
                                                                    =
                                                                    let uu____15184
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu____15184) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____15183 in
                                                                    {
                                                                    FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                    FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.lift_wp
                                                                    =
                                                                    uu____15180;
                                                                    FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    } in
                                                                   let uu____15191
                                                                    =
                                                                    mk_sigelt
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu____15191
                                                                 else
                                                                   FStar_Pervasives_Native.None in
                                                               let uu____15193
                                                                 =
                                                                 let uu____15196
                                                                   =
                                                                   let uu____15199
                                                                    =
                                                                    FStar_ST.op_Bang
                                                                    sigelts in
                                                                   FStar_List.rev
                                                                    uu____15199 in
                                                                 FStar_List.append
                                                                   uu____15196
                                                                   sigelts' in
                                                               (uu____15193,
                                                                 ed2,
                                                                 lift_from_pure_opt))))))))))))))))))