open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ;}
let empty:
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const }
let gen_wps_for_free:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts,FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.EraseUniverses] env wp_a in
            let a1 =
              let uu___100_75 = a in
              let uu____76 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___100_75.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___100_75.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____76
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____86 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____86
             then
               (d "Elaborating extra WP combinators";
                (let uu____88 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____88))
             else ());
            (let rec collect_binders t =
               let uu____100 =
                 let uu____101 =
                   let uu____106 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____106 in
                 uu____101.FStar_Syntax_Syntax.n in
               match uu____100 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____145) -> t1
                     | uu____158 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____163 = collect_binders rest in
                   FStar_List.append bs uu____163
               | FStar_Syntax_Syntax.Tm_type uu____174 -> []
               | uu____179 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____197 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____197 FStar_Syntax_Util.name_binders in
             (let uu____217 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____217
              then
                let uu____218 =
                  let uu____219 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____219 in
                d uu____218
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                (FStar_Syntax_Syntax.mk x) FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____247 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____247 with
                | (sigelt,fv) ->
                    ((let uu____255 =
                        let uu____258 = FStar_ST.read sigelts in sigelt ::
                          uu____258 in
                      FStar_ST.write sigelts uu____255);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____292  ->
                     match uu____292 with
                     | (t,b) ->
                         let uu____303 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____303)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____332 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____332)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____353 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____353) in
              let uu____354 =
                let uu____373 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____401 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____401 in
                    let uu____406 =
                      let uu____407 =
                        let uu____414 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____415 =
                          let uu____418 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____418] in
                        uu____414 :: uu____415 in
                      FStar_List.append binders uu____407 in
                    FStar_Syntax_Util.abs uu____406 body
                      FStar_Pervasives_Native.None in
                  let uu____433 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____434 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____433, uu____434) in
                match uu____373 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____478 =
                        let uu____479 =
                          let uu____498 =
                            let uu____505 =
                              FStar_List.map
                                (fun uu____520  ->
                                   match uu____520 with
                                   | (bv,uu____530) ->
                                       let uu____531 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____532 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____531, uu____532)) binders in
                            let uu____533 =
                              let uu____540 =
                                let uu____545 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____546 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____545, uu____546) in
                              let uu____547 =
                                let uu____554 =
                                  let uu____559 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____559) in
                                [uu____554] in
                              uu____540 :: uu____547 in
                            FStar_List.append uu____505 uu____533 in
                          (fv, uu____498) in
                        FStar_Syntax_Syntax.Tm_app uu____479 in
                      mk1 uu____478 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____354 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____632 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____632 in
                    let ret1 =
                      let uu____646 =
                        let uu____657 =
                          let uu____658 =
                            let uu____663 =
                              let uu____664 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____664 in
                            FStar_Syntax_Syntax.mk_Total uu____663 in
                          FStar_Syntax_Util.lcomp_of_comp uu____658 in
                        FStar_Util.Inl uu____657 in
                      FStar_Pervasives_Native.Some uu____646 in
                    let body =
                      let uu____682 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____682 ret1 in
                    let uu____683 =
                      let uu____684 = mk_all_implicit binders in
                      let uu____691 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____684 uu____691 in
                    FStar_Syntax_Util.abs uu____683 body ret1 in
                  let c_pure1 =
                    let uu____719 = mk_lid "pure" in
                    register env1 uu____719 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____724 =
                        let uu____725 =
                          let uu____726 =
                            let uu____733 =
                              let uu____734 =
                                let uu____735 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____735 in
                              FStar_Syntax_Syntax.mk_binder uu____734 in
                            [uu____733] in
                          let uu____736 =
                            let uu____741 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____741 in
                          FStar_Syntax_Util.arrow uu____726 uu____736 in
                        mk_gctx uu____725 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____724 in
                    let r =
                      let uu____743 =
                        let uu____744 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____744 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____743 in
                    let ret1 =
                      let uu____758 =
                        let uu____769 =
                          let uu____770 =
                            let uu____775 =
                              let uu____776 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____776 in
                            FStar_Syntax_Syntax.mk_Total uu____775 in
                          FStar_Syntax_Util.lcomp_of_comp uu____770 in
                        FStar_Util.Inl uu____769 in
                      FStar_Pervasives_Native.Some uu____758 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____802 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____807 =
                          let uu____818 =
                            let uu____821 =
                              let uu____822 =
                                let uu____823 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____823
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____822 in
                            [uu____821] in
                          FStar_List.append gamma_as_args uu____818 in
                        FStar_Syntax_Util.mk_app uu____802 uu____807 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____828 =
                      let uu____829 = mk_all_implicit binders in
                      let uu____836 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____829 uu____836 in
                    FStar_Syntax_Util.abs uu____828 outer_body ret1 in
                  let c_app1 =
                    let uu____872 = mk_lid "app" in
                    register env1 uu____872 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____881 =
                        let uu____888 =
                          let uu____889 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____889 in
                        [uu____888] in
                      let uu____890 =
                        let uu____895 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____895 in
                      FStar_Syntax_Util.arrow uu____881 uu____890 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____898 =
                        let uu____899 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____899 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____898 in
                    let ret1 =
                      let uu____913 =
                        let uu____924 =
                          let uu____925 =
                            let uu____930 =
                              let uu____931 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____931 in
                            FStar_Syntax_Syntax.mk_Total uu____930 in
                          FStar_Syntax_Util.lcomp_of_comp uu____925 in
                        FStar_Util.Inl uu____924 in
                      FStar_Pervasives_Native.Some uu____913 in
                    let uu____948 =
                      let uu____949 = mk_all_implicit binders in
                      let uu____956 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____949 uu____956 in
                    let uu____991 =
                      let uu____992 =
                        let uu____1003 =
                          let uu____1006 =
                            let uu____1011 =
                              let uu____1022 =
                                let uu____1025 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____1025] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1022 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1011 in
                          let uu____1026 =
                            let uu____1033 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____1033] in
                          uu____1006 :: uu____1026 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1003 in
                      FStar_Syntax_Util.mk_app c_app1 uu____992 in
                    FStar_Syntax_Util.abs uu____948 uu____991 ret1 in
                  let c_lift11 =
                    let uu____1039 = mk_lid "lift1" in
                    register env1 uu____1039 c_lift1 in
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
                      let uu____1049 =
                        let uu____1056 =
                          let uu____1057 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1057 in
                        let uu____1058 =
                          let uu____1061 =
                            let uu____1062 =
                              FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____1062 in
                          [uu____1061] in
                        uu____1056 :: uu____1058 in
                      let uu____1063 =
                        let uu____1068 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1068 in
                      FStar_Syntax_Util.arrow uu____1049 uu____1063 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1071 =
                        let uu____1072 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1072 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1071 in
                    let a2 =
                      let uu____1074 =
                        let uu____1075 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____1075 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1074 in
                    let ret1 =
                      let uu____1089 =
                        let uu____1100 =
                          let uu____1101 =
                            let uu____1106 =
                              let uu____1107 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____1107 in
                            FStar_Syntax_Syntax.mk_Total uu____1106 in
                          FStar_Syntax_Util.lcomp_of_comp uu____1101 in
                        FStar_Util.Inl uu____1100 in
                      FStar_Pervasives_Native.Some uu____1089 in
                    let uu____1124 =
                      let uu____1125 = mk_all_implicit binders in
                      let uu____1132 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1125 uu____1132 in
                    let uu____1175 =
                      let uu____1176 =
                        let uu____1187 =
                          let uu____1190 =
                            let uu____1195 =
                              let uu____1206 =
                                let uu____1209 =
                                  let uu____1214 =
                                    let uu____1225 =
                                      let uu____1228 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1228] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1225 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1214 in
                                let uu____1229 =
                                  let uu____1236 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1236] in
                                uu____1209 :: uu____1229 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1206 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1195 in
                          let uu____1241 =
                            let uu____1248 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1248] in
                          uu____1190 :: uu____1241 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1187 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1176 in
                    FStar_Syntax_Util.abs uu____1124 uu____1175 ret1 in
                  let c_lift21 =
                    let uu____1254 = mk_lid "lift2" in
                    register env1 uu____1254 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1263 =
                        let uu____1270 =
                          let uu____1271 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1271 in
                        [uu____1270] in
                      let uu____1272 =
                        let uu____1277 =
                          let uu____1278 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1278 in
                        FStar_Syntax_Syntax.mk_Total uu____1277 in
                      FStar_Syntax_Util.arrow uu____1263 uu____1272 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1293 =
                        let uu____1304 =
                          let uu____1305 =
                            let uu____1310 =
                              let uu____1311 =
                                let uu____1312 =
                                  let uu____1319 =
                                    let uu____1320 =
                                      FStar_Syntax_Syntax.bv_to_name t1 in
                                    FStar_Syntax_Syntax.null_binder
                                      uu____1320 in
                                  [uu____1319] in
                                let uu____1321 =
                                  let uu____1326 =
                                    FStar_Syntax_Syntax.bv_to_name t2 in
                                  FStar_Syntax_Syntax.mk_GTotal uu____1326 in
                                FStar_Syntax_Util.arrow uu____1312 uu____1321 in
                              mk_ctx uu____1311 in
                            FStar_Syntax_Syntax.mk_Total uu____1310 in
                          FStar_Syntax_Util.lcomp_of_comp uu____1305 in
                        FStar_Util.Inl uu____1304 in
                      FStar_Pervasives_Native.Some uu____1293 in
                    let e1 =
                      let uu____1344 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1344 in
                    let body =
                      let uu____1346 =
                        let uu____1347 =
                          let uu____1354 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1354] in
                        FStar_List.append gamma uu____1347 in
                      let uu____1359 =
                        let uu____1360 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1365 =
                          let uu____1376 =
                            let uu____1377 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1377 in
                          let uu____1378 = args_of_binders1 gamma in
                          uu____1376 :: uu____1378 in
                        FStar_Syntax_Util.mk_app uu____1360 uu____1365 in
                      FStar_Syntax_Util.abs uu____1346 uu____1359 ret1 in
                    let uu____1381 =
                      let uu____1382 = mk_all_implicit binders in
                      let uu____1389 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1382 uu____1389 in
                    FStar_Syntax_Util.abs uu____1381 body ret1 in
                  let c_push1 =
                    let uu____1421 = mk_lid "push" in
                    register env1 uu____1421 c_push in
                  let ret_tot_wp_a =
                    let uu____1435 =
                      let uu____1446 =
                        let uu____1447 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____1447 in
                      FStar_Util.Inl uu____1446 in
                    FStar_Pervasives_Native.Some uu____1435 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1492 =
                        let uu____1493 =
                          let uu____1512 = args_of_binders1 binders in
                          (c, uu____1512) in
                        FStar_Syntax_Syntax.Tm_app uu____1493 in
                      mk1 uu____1492
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1524 =
                        let uu____1525 =
                          let uu____1532 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1533 =
                            let uu____1536 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1536] in
                          uu____1532 :: uu____1533 in
                        let uu____1537 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1525 uu____1537 in
                      FStar_Syntax_Syntax.mk_Total uu____1524 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1543 =
                      let uu____1544 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1544 in
                    let uu____1555 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1557 =
                        let uu____1562 =
                          let uu____1573 =
                            let uu____1576 =
                              let uu____1581 =
                                let uu____1592 =
                                  let uu____1593 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1593 in
                                [uu____1592] in
                              FStar_Syntax_Util.mk_app l_ite uu____1581 in
                            [uu____1576] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1573 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1562 in
                      FStar_Syntax_Util.ascribe uu____1557
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1543 uu____1555
                      (FStar_Pervasives_Native.Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1641 = mk_lid "wp_if_then_else" in
                    register env1 uu____1641 wp_if_then_else in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1 in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None in
                    let body =
                      let uu____1656 =
                        let uu____1667 =
                          let uu____1670 =
                            let uu____1675 =
                              let uu____1686 =
                                let uu____1689 =
                                  let uu____1694 =
                                    let uu____1705 =
                                      let uu____1706 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1706 in
                                    [uu____1705] in
                                  FStar_Syntax_Util.mk_app l_and uu____1694 in
                                [uu____1689] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1686 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1675 in
                          let uu____1715 =
                            let uu____1722 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1722] in
                          uu____1670 :: uu____1715 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1667 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1656 in
                    let uu____1727 =
                      let uu____1728 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1728 in
                    FStar_Syntax_Util.abs uu____1727 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1740 = mk_lid "wp_assert" in
                    register env1 uu____1740 wp_assert in
                  let wp_assert2 = mk_generic_app wp_assert1 in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None in
                    let body =
                      let uu____1755 =
                        let uu____1766 =
                          let uu____1769 =
                            let uu____1774 =
                              let uu____1785 =
                                let uu____1788 =
                                  let uu____1793 =
                                    let uu____1804 =
                                      let uu____1805 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1805 in
                                    [uu____1804] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1793 in
                                [uu____1788] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1785 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1774 in
                          let uu____1814 =
                            let uu____1821 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1821] in
                          uu____1769 :: uu____1814 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1766 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1755 in
                    let uu____1826 =
                      let uu____1827 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1827 in
                    FStar_Syntax_Util.abs uu____1826 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1839 = mk_lid "wp_assume" in
                    register env1 uu____1839 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1852 =
                        let uu____1859 =
                          let uu____1860 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1860 in
                        [uu____1859] in
                      let uu____1861 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1852 uu____1861 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1872 =
                        let uu____1883 =
                          let uu____1886 =
                            let uu____1891 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1891 in
                          let uu____1902 =
                            let uu____1909 =
                              let uu____1914 =
                                let uu____1925 =
                                  let uu____1928 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1928] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1925 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1914 in
                            [uu____1909] in
                          uu____1886 :: uu____1902 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1883 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1872 in
                    let uu____1941 =
                      let uu____1942 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1942 in
                    FStar_Syntax_Util.abs uu____1941 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1954 = mk_lid "wp_close" in
                    register env1 uu____1954 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1973 =
                      let uu____1984 =
                        let uu____1985 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1985 in
                      FStar_Util.Inl uu____1984 in
                    FStar_Pervasives_Native.Some uu____1973 in
                  let ret_gtot_type =
                    let uu____2023 =
                      let uu____2034 =
                        let uu____2035 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____2035 in
                      FStar_Util.Inl uu____2034 in
                    FStar_Pervasives_Native.Some uu____2023 in
                  let mk_forall1 x body =
                    let uu____2067 =
                      let uu____2072 =
                        let uu____2073 =
                          let uu____2092 =
                            let uu____2095 =
                              let uu____2096 =
                                let uu____2097 =
                                  let uu____2098 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____2098] in
                                FStar_Syntax_Util.abs uu____2097 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____2096 in
                            [uu____2095] in
                          (FStar_Syntax_Util.tforall, uu____2092) in
                        FStar_Syntax_Syntax.Tm_app uu____2073 in
                      FStar_Syntax_Syntax.mk uu____2072 in
                    uu____2067 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____2109 =
                      let uu____2110 = FStar_Syntax_Subst.compress t in
                      uu____2110.FStar_Syntax_Syntax.n in
                    match uu____2109 with
                    | FStar_Syntax_Syntax.Tm_type uu____2115 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2142  ->
                              match uu____2142 with
                              | (b,uu____2148) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____2149 -> true in
                  let rec is_monotonic t =
                    let uu____2154 =
                      let uu____2155 = FStar_Syntax_Subst.compress t in
                      uu____2155.FStar_Syntax_Syntax.n in
                    match uu____2154 with
                    | FStar_Syntax_Syntax.Tm_type uu____2160 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____2187  ->
                              match uu____2187 with
                              | (b,uu____2193) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____2194 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____2266 =
                      let uu____2267 = FStar_Syntax_Subst.compress t1 in
                      uu____2267.FStar_Syntax_Syntax.n in
                    match uu____2266 with
                    | FStar_Syntax_Syntax.Tm_type uu____2272 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2275);
                                      FStar_Syntax_Syntax.tk = uu____2276;
                                      FStar_Syntax_Syntax.pos = uu____2277;
                                      FStar_Syntax_Syntax.vars = uu____2278;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2322 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2322
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2325 =
                              let uu____2330 =
                                let uu____2341 =
                                  let uu____2342 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2342 in
                                [uu____2341] in
                              FStar_Syntax_Util.mk_app x uu____2330 in
                            let uu____2343 =
                              let uu____2348 =
                                let uu____2359 =
                                  let uu____2360 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2360 in
                                [uu____2359] in
                              FStar_Syntax_Util.mk_app y uu____2348 in
                            mk_rel1 b uu____2325 uu____2343 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2365 =
                               let uu____2366 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2371 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2366 uu____2371 in
                             let uu____2376 =
                               let uu____2377 =
                                 let uu____2382 =
                                   let uu____2393 =
                                     let uu____2394 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2394 in
                                   [uu____2393] in
                                 FStar_Syntax_Util.mk_app x uu____2382 in
                               let uu____2395 =
                                 let uu____2400 =
                                   let uu____2411 =
                                     let uu____2412 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2412 in
                                   [uu____2411] in
                                 FStar_Syntax_Util.mk_app y uu____2400 in
                               mk_rel1 b uu____2377 uu____2395 in
                             FStar_Syntax_Util.mk_imp uu____2365 uu____2376 in
                           let uu____2413 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2413)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2416);
                                      FStar_Syntax_Syntax.tk = uu____2417;
                                      FStar_Syntax_Syntax.pos = uu____2418;
                                      FStar_Syntax_Syntax.vars = uu____2419;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2463 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2463
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2466 =
                              let uu____2471 =
                                let uu____2482 =
                                  let uu____2483 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2483 in
                                [uu____2482] in
                              FStar_Syntax_Util.mk_app x uu____2471 in
                            let uu____2484 =
                              let uu____2489 =
                                let uu____2500 =
                                  let uu____2501 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2501 in
                                [uu____2500] in
                              FStar_Syntax_Util.mk_app y uu____2489 in
                            mk_rel1 b uu____2466 uu____2484 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2506 =
                               let uu____2507 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2512 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2507 uu____2512 in
                             let uu____2517 =
                               let uu____2518 =
                                 let uu____2523 =
                                   let uu____2534 =
                                     let uu____2535 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2535 in
                                   [uu____2534] in
                                 FStar_Syntax_Util.mk_app x uu____2523 in
                               let uu____2536 =
                                 let uu____2541 =
                                   let uu____2552 =
                                     let uu____2553 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2553 in
                                   [uu____2552] in
                                 FStar_Syntax_Util.mk_app y uu____2541 in
                               mk_rel1 b uu____2518 uu____2536 in
                             FStar_Syntax_Util.mk_imp uu____2506 uu____2517 in
                           let uu____2554 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2554)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___101_2591 = t1 in
                          let uu____2592 =
                            let uu____2593 =
                              let uu____2608 =
                                let uu____2609 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2609 in
                              ([binder], uu____2608) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2593 in
                          {
                            FStar_Syntax_Syntax.n = uu____2592;
                            FStar_Syntax_Syntax.tk =
                              (uu___101_2591.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___101_2591.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___101_2591.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2624 ->
                        failwith "unhandled arrow"
                    | uu____2639 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2654 =
                        let uu____2655 = FStar_Syntax_Subst.compress t1 in
                        uu____2655.FStar_Syntax_Syntax.n in
                      match uu____2654 with
                      | FStar_Syntax_Syntax.Tm_type uu____2660 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2691 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2691
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2712 =
                                let uu____2713 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2713 i in
                              FStar_Syntax_Syntax.fvar uu____2712
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2748 =
                            let uu____2755 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2763  ->
                                     match uu____2763 with
                                     | (t2,q) ->
                                         let uu____2770 = project i x in
                                         let uu____2771 = project i y in
                                         mk_stronger t2 uu____2770 uu____2771)
                                args in
                            match uu____2755 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2748 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2798);
                                      FStar_Syntax_Syntax.tk = uu____2799;
                                      FStar_Syntax_Syntax.pos = uu____2800;
                                      FStar_Syntax_Syntax.vars = uu____2801;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2842  ->
                                   match uu____2842 with
                                   | (bv,q) ->
                                       let uu____2849 =
                                         let uu____2850 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2850 in
                                       FStar_Syntax_Syntax.gen_bv uu____2849
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2855 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2855) bvs in
                          let body =
                            let uu____2857 = FStar_Syntax_Util.mk_app x args in
                            let uu____2858 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2857 uu____2858 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2863);
                                      FStar_Syntax_Syntax.tk = uu____2864;
                                      FStar_Syntax_Syntax.pos = uu____2865;
                                      FStar_Syntax_Syntax.vars = uu____2866;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2907  ->
                                   match uu____2907 with
                                   | (bv,q) ->
                                       let uu____2914 =
                                         let uu____2915 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2915 in
                                       FStar_Syntax_Syntax.gen_bv uu____2914
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2920 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2920) bvs in
                          let body =
                            let uu____2922 = FStar_Syntax_Util.mk_app x args in
                            let uu____2923 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2922 uu____2923 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2926 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2928 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2929 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2930 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2928 uu____2929 uu____2930 in
                    let uu____2931 =
                      let uu____2932 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2932 in
                    FStar_Syntax_Util.abs uu____2931 body ret_tot_type in
                  let stronger1 =
                    let uu____2960 = mk_lid "stronger" in
                    register env1 uu____2960 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2968 = FStar_Util.prefix gamma in
                    match uu____2968 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____3013 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____3013 in
                          let uu____3018 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____3018 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____3030 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____3030 in
                              let guard_free1 =
                                let uu____3042 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____3042 in
                              let pat =
                                let uu____3048 =
                                  let uu____3059 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____3059] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____3048 in
                              let pattern_guarded_body =
                                let uu____3065 =
                                  let uu____3066 =
                                    let uu____3075 =
                                      let uu____3076 =
                                        let uu____3089 =
                                          let uu____3092 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____3092] in
                                        [uu____3089] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____3076 in
                                    (body, uu____3075) in
                                  FStar_Syntax_Syntax.Tm_meta uu____3066 in
                                mk1 uu____3065 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____3097 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____3101 =
                            let uu____3102 =
                              let uu____3103 =
                                let uu____3104 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____3109 =
                                  let uu____3120 = args_of_binders1 wp_args in
                                  let uu____3123 =
                                    let uu____3126 =
                                      let uu____3127 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____3127 in
                                    [uu____3126] in
                                  FStar_List.append uu____3120 uu____3123 in
                                FStar_Syntax_Util.mk_app uu____3104
                                  uu____3109 in
                              FStar_Syntax_Util.mk_imp equiv uu____3103 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____3102 in
                          FStar_Syntax_Util.abs gamma uu____3101
                            ret_gtot_type in
                        let uu____3128 =
                          let uu____3129 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____3129 in
                        FStar_Syntax_Util.abs uu____3128 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____3141 = mk_lid "wp_ite" in
                    register env1 uu____3141 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____3149 = FStar_Util.prefix gamma in
                    match uu____3149 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____3192 =
                            let uu____3193 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____3198 =
                              let uu____3209 =
                                let uu____3210 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____3210 in
                              [uu____3209] in
                            FStar_Syntax_Util.mk_app uu____3193 uu____3198 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____3192 in
                        let uu____3211 =
                          let uu____3212 =
                            let uu____3219 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____3219 gamma in
                          FStar_List.append binders uu____3212 in
                        FStar_Syntax_Util.abs uu____3211 body ret_gtot_type in
                  let null_wp1 =
                    let uu____3235 = mk_lid "null_wp" in
                    register env1 uu____3235 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____3248 =
                        let uu____3259 =
                          let uu____3262 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____3263 =
                            let uu____3266 =
                              let uu____3271 =
                                let uu____3282 =
                                  let uu____3283 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____3283 in
                                [uu____3282] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3271 in
                            let uu____3284 =
                              let uu____3291 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____3291] in
                            uu____3266 :: uu____3284 in
                          uu____3262 :: uu____3263 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____3259 in
                      FStar_Syntax_Util.mk_app stronger2 uu____3248 in
                    let uu____3296 =
                      let uu____3297 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____3297 in
                    FStar_Syntax_Util.abs uu____3296 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____3309 = mk_lid "wp_trivial" in
                    register env1 uu____3309 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____3316 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____3316
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____3321 =
                      let uu____3324 = FStar_ST.read sigelts in
                      FStar_List.rev uu____3324 in
                    let uu____3331 =
                      let uu___102_3332 = ed in
                      let uu____3333 =
                        let uu____3334 = c wp_if_then_else2 in
                        ([], uu____3334) in
                      let uu____3337 =
                        let uu____3338 = c wp_ite2 in ([], uu____3338) in
                      let uu____3341 =
                        let uu____3342 = c stronger2 in ([], uu____3342) in
                      let uu____3345 =
                        let uu____3346 = c wp_close2 in ([], uu____3346) in
                      let uu____3349 =
                        let uu____3350 = c wp_assert2 in ([], uu____3350) in
                      let uu____3353 =
                        let uu____3354 = c wp_assume2 in ([], uu____3354) in
                      let uu____3357 =
                        let uu____3358 = c null_wp2 in ([], uu____3358) in
                      let uu____3361 =
                        let uu____3362 = c wp_trivial2 in ([], uu____3362) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___102_3332.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___102_3332.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___102_3332.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___102_3332.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___102_3332.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___102_3332.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___102_3332.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3333;
                        FStar_Syntax_Syntax.ite_wp = uu____3337;
                        FStar_Syntax_Syntax.stronger = uu____3341;
                        FStar_Syntax_Syntax.close_wp = uu____3345;
                        FStar_Syntax_Syntax.assert_p = uu____3349;
                        FStar_Syntax_Syntax.assume_p = uu____3353;
                        FStar_Syntax_Syntax.null_wp = uu____3357;
                        FStar_Syntax_Syntax.trivial = uu____3361;
                        FStar_Syntax_Syntax.repr =
                          (uu___102_3332.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___102_3332.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___102_3332.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___102_3332.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____3321, uu____3331)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___103_3376 = dmff_env in
      {
        env = env';
        subst = (uu___103_3376.subst);
        tc_const = (uu___103_3376.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____3389 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____3401 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___89_3411  ->
    match uu___89_3411 with
    | FStar_Syntax_Syntax.Total (t,uu____3413) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___88_3429  ->
                match uu___88_3429 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3430 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____3432 =
          let uu____3433 =
            let uu____3434 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3434 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3433 in
        failwith uu____3432
    | FStar_Syntax_Syntax.GTotal uu____3435 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___90_3448  ->
    match uu___90_3448 with
    | N t ->
        let uu____3450 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____3450
    | M t ->
        let uu____3452 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____3452
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3456,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____3458;
                      FStar_Syntax_Syntax.pos = uu____3459;
                      FStar_Syntax_Syntax.vars = uu____3460;_})
        -> nm_of_comp n2
    | uu____3481 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____3497 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____3497 with | M uu____3498 -> true | N uu____3499 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3503 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____3515 =
        let uu____3522 =
          let uu____3523 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3523 in
        [uu____3522] in
      let uu____3524 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____3515 uu____3524 in
    let uu____3529 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____3529
let rec mk_star_to_type:
  (FStar_Syntax_Syntax.term' ->
     (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
       FStar_Syntax_Syntax.syntax)
    ->
    env ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        mk1
          (let uu____3580 =
             let uu____3595 =
               let uu____3602 =
                 let uu____3607 =
                   let uu____3608 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____3608 in
                 let uu____3609 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____3607, uu____3609) in
               [uu____3602] in
             let uu____3618 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____3595, uu____3618) in
           FStar_Syntax_Syntax.Tm_arrow uu____3580)
and star_type':
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk1 in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3654) ->
          let binders1 =
            FStar_List.map
              (fun uu____3690  ->
                 match uu____3690 with
                 | (bv,aqual) ->
                     let uu____3701 =
                       let uu___104_3702 = bv in
                       let uu____3703 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___104_3702.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___104_3702.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3703
                       } in
                     (uu____3701, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3708,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3710);
                             FStar_Syntax_Syntax.tk = uu____3711;
                             FStar_Syntax_Syntax.pos = uu____3712;
                             FStar_Syntax_Syntax.vars = uu____3713;_})
               ->
               let uu____3746 =
                 let uu____3747 =
                   let uu____3762 =
                     let uu____3763 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3763 in
                   (binders1, uu____3762) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3747 in
               mk1 uu____3746
           | uu____3770 ->
               let uu____3771 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3771 with
                | N hn ->
                    let uu____3773 =
                      let uu____3774 =
                        let uu____3789 =
                          let uu____3790 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3790 in
                        (binders1, uu____3789) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3774 in
                    mk1 uu____3773
                | M a ->
                    let uu____3798 =
                      let uu____3799 =
                        let uu____3814 =
                          let uu____3821 =
                            let uu____3828 =
                              let uu____3833 =
                                let uu____3834 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3834 in
                              let uu____3835 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3833, uu____3835) in
                            [uu____3828] in
                          FStar_List.append binders1 uu____3821 in
                        let uu____3848 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3814, uu____3848) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3799 in
                    mk1 uu____3798))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3922 = f x in
                    FStar_Util.string_builder_append strb uu____3922);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3926 = f x1 in
                         FStar_Util.string_builder_append strb uu____3926))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3928 = FStar_Syntax_Print.term_to_string t2 in
            let uu____3929 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____3928 uu____3929 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3937 =
              let uu____3938 = FStar_Syntax_Subst.compress ty in
              uu____3938.FStar_Syntax_Syntax.n in
            match uu____3937 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3965 =
                  let uu____3966 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3966 in
                if uu____3965
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3983 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3983 s in
                       let uu____3986 =
                         let uu____3987 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3987 in
                       if uu____3986
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____3990 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3990 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____4007  ->
                                  match uu____4007 with
                                  | (bv,uu____4017) ->
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
                   with | Not_found  -> false)
            | uu____4032 ->
                ((let uu____4034 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____4034);
                 false) in
          let rec is_valid_application head2 =
            let uu____4039 =
              let uu____4040 = FStar_Syntax_Subst.compress head2 in
              uu____4040.FStar_Syntax_Syntax.n in
            match uu____4039 with
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
                  (let uu____4046 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____4046)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv when
                is_non_dependent_arrow
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty
                  (FStar_List.length args)
                ->
                let res =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Inlining;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                (match res.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_app uu____4061 -> true
                 | uu____4080 ->
                     ((let uu____4082 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____4082);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____4083 -> true
            | FStar_Syntax_Syntax.Tm_name uu____4084 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____4086) ->
                is_valid_application t2
            | uu____4095 -> false in
          let uu____4096 = is_valid_application head1 in
          if uu____4096
          then
            let uu____4097 =
              let uu____4098 =
                let uu____4117 =
                  FStar_List.map
                    (fun uu____4136  ->
                       match uu____4136 with
                       | (t2,qual) ->
                           let uu____4159 = star_type' env t2 in
                           (uu____4159, qual)) args in
                (head1, uu____4117) in
              FStar_Syntax_Syntax.Tm_app uu____4098 in
            mk1 uu____4097
          else
            (let uu____4171 =
               let uu____4172 =
                 let uu____4173 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____4173 in
               FStar_Errors.Err uu____4172 in
             raise uu____4171)
      | FStar_Syntax_Syntax.Tm_bvar uu____4174 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____4175 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____4176 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____4177 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____4225 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____4225 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___107_4233 = env in
                 let uu____4234 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____4234;
                   subst = (uu___107_4233.subst);
                   tc_const = (uu___107_4233.tc_const)
                 } in
               let repr2 = star_type' env1 repr1 in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)] in
          let t3 = FStar_Syntax_Subst.subst subst1 t2 in
          let t4 = star_type' env t3 in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))] in
          let t5 = FStar_Syntax_Subst.subst subst2 t4 in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___108_4257 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___108_4257.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___108_4257.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____4268 =
            let uu____4269 =
              let uu____4278 = star_type' env t2 in (uu____4278, m) in
            FStar_Syntax_Syntax.Tm_meta uu____4269 in
          mk1 uu____4268
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____4350 =
            let uu____4351 =
              let uu____4386 = star_type' env e in
              let uu____4387 =
                let uu____4406 =
                  let uu____4415 = star_type' env t2 in
                  FStar_Util.Inl uu____4415 in
                (uu____4406, FStar_Pervasives_Native.None) in
              (uu____4386, uu____4387, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____4351 in
          mk1 uu____4350
      | FStar_Syntax_Syntax.Tm_ascribed uu____4458 ->
          let uu____4493 =
            let uu____4494 =
              let uu____4495 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____4495 in
            FStar_Errors.Err uu____4494 in
          raise uu____4493
      | FStar_Syntax_Syntax.Tm_refine uu____4496 ->
          let uu____4505 =
            let uu____4506 =
              let uu____4507 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4507 in
            FStar_Errors.Err uu____4506 in
          raise uu____4505
      | FStar_Syntax_Syntax.Tm_uinst uu____4508 ->
          let uu____4517 =
            let uu____4518 =
              let uu____4519 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4519 in
            FStar_Errors.Err uu____4518 in
          raise uu____4517
      | FStar_Syntax_Syntax.Tm_constant uu____4520 ->
          let uu____4521 =
            let uu____4522 =
              let uu____4523 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4523 in
            FStar_Errors.Err uu____4522 in
          raise uu____4521
      | FStar_Syntax_Syntax.Tm_match uu____4524 ->
          let uu____4555 =
            let uu____4556 =
              let uu____4557 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4557 in
            FStar_Errors.Err uu____4556 in
          raise uu____4555
      | FStar_Syntax_Syntax.Tm_let uu____4558 ->
          let uu____4573 =
            let uu____4574 =
              let uu____4575 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4575 in
            FStar_Errors.Err uu____4574 in
          raise uu____4573
      | FStar_Syntax_Syntax.Tm_uvar uu____4576 ->
          let uu____4593 =
            let uu____4594 =
              let uu____4595 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4595 in
            FStar_Errors.Err uu____4594 in
          raise uu____4593
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4596 =
            let uu____4597 =
              let uu____4598 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4598 in
            FStar_Errors.Err uu____4597 in
          raise uu____4596
      | FStar_Syntax_Syntax.Tm_delayed uu____4599 -> failwith "impossible"
let is_monadic uu___92_4656 =
  match uu___92_4656 with
  | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
  | FStar_Pervasives_Native.Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____4679;
        FStar_Syntax_Syntax.res_typ = uu____4680;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____4682;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_4713  ->
              match uu___91_4713 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____4714 -> false))
  | FStar_Pervasives_Native.Some (FStar_Util.Inr (uu____4715,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_4739  ->
              match uu___91_4739 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____4740 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____4744 =
      let uu____4745 = FStar_Syntax_Subst.compress t in
      uu____4745.FStar_Syntax_Syntax.n in
    match uu____4744 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4781 =
            let uu____4782 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____4782 in
          is_C uu____4781 in
        if r
        then
          ((let uu____4804 =
              let uu____4805 =
                FStar_List.for_all
                  (fun uu____4810  ->
                     match uu____4810 with | (h,uu____4816) -> is_C h) args in
              Prims.op_Negation uu____4805 in
            if uu____4804 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4820 =
              let uu____4821 =
                FStar_List.for_all
                  (fun uu____4826  ->
                     match uu____4826 with
                     | (h,uu____4832) ->
                         let uu____4833 = is_C h in
                         Prims.op_Negation uu____4833) args in
              Prims.op_Negation uu____4821 in
            if uu____4820 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4857 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4857 with
         | M t1 ->
             ((let uu____4860 = is_C t1 in
               if uu____4860 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4864) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4874) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4884,uu____4885) -> is_C t1
    | uu____4942 -> false
let mk_return:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk1 env t in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type in
        let body =
          let uu____4971 =
            let uu____4972 =
              let uu____4991 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4992 =
                let uu____4999 =
                  let uu____5004 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____5004) in
                [uu____4999] in
              (uu____4991, uu____4992) in
            FStar_Syntax_Syntax.Tm_app uu____4972 in
          mk1 uu____4971 in
        let uu____5019 =
          let uu____5020 = FStar_Syntax_Syntax.mk_binder p in [uu____5020] in
        let uu____5021 =
          let uu____5034 =
            let uu____5045 =
              let uu____5046 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____5046 in
            FStar_Util.Inl uu____5045 in
          FStar_Pervasives_Native.Some uu____5034 in
        FStar_Syntax_Util.abs uu____5019 body uu____5021
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___93_5069  ->
    match uu___93_5069 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5070 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____5257 =
          match uu____5257 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____5288 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____5289 =
                       let uu____5290 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____5290 in
                     Prims.op_Negation uu____5289) in
                if uu____5288
                then
                  let uu____5291 =
                    let uu____5292 =
                      let uu____5293 = FStar_Syntax_Print.term_to_string e in
                      let uu____5294 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____5295 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____5293 uu____5294 uu____5295 in
                    FStar_Errors.Err uu____5292 in
                  raise uu____5291
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____5312 = mk_return env t1 s_e in
                     ((M t1), uu____5312, u_e)))
               | (M t1,N t2) ->
                   let uu____5315 =
                     let uu____5316 =
                       let uu____5317 = FStar_Syntax_Print.term_to_string e in
                       let uu____5318 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____5319 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____5317 uu____5318 uu____5319 in
                     FStar_Errors.Err uu____5316 in
                   raise uu____5315) in
        let ensure_m env1 e2 =
          let strip_m uu___94_5360 =
            match uu___94_5360 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____5376 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____5396 =
                let uu____5397 =
                  let uu____5402 =
                    let uu____5403 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____5403 in
                  (uu____5402, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____5397 in
              raise uu____5396
          | M uu____5410 ->
              let uu____5411 = check env1 e2 context_nm in strip_m uu____5411 in
        let uu____5418 =
          let uu____5419 = FStar_Syntax_Subst.compress e in
          uu____5419.FStar_Syntax_Syntax.n in
        match uu____5418 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5430 ->
            let uu____5431 = infer env e in return_if uu____5431
        | FStar_Syntax_Syntax.Tm_name uu____5438 ->
            let uu____5439 = infer env e in return_if uu____5439
        | FStar_Syntax_Syntax.Tm_fvar uu____5446 ->
            let uu____5447 = infer env e in return_if uu____5447
        | FStar_Syntax_Syntax.Tm_abs uu____5454 ->
            let uu____5483 = infer env e in return_if uu____5483
        | FStar_Syntax_Syntax.Tm_constant uu____5490 ->
            let uu____5491 = infer env e in return_if uu____5491
        | FStar_Syntax_Syntax.Tm_app uu____5498 ->
            let uu____5517 = infer env e in return_if uu____5517
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5601) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5611) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5621,uu____5622) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5679 ->
            let uu____5694 =
              let uu____5695 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5695 in
            failwith uu____5694
        | FStar_Syntax_Syntax.Tm_type uu____5702 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5709 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5730 ->
            let uu____5739 =
              let uu____5740 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5740 in
            failwith uu____5739
        | FStar_Syntax_Syntax.Tm_uvar uu____5747 ->
            let uu____5764 =
              let uu____5765 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5765 in
            failwith uu____5764
        | FStar_Syntax_Syntax.Tm_delayed uu____5772 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5817 =
              let uu____5818 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5818 in
            failwith uu____5817
and infer:
  env ->
    FStar_Syntax_Syntax.term ->
      (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
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
      let uu____5844 =
        let uu____5845 = FStar_Syntax_Subst.compress e in
        uu____5845.FStar_Syntax_Syntax.n in
      match uu____5844 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___109_5915 = env in
            let uu____5916 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____5916;
              subst = (uu___109_5915.subst);
              tc_const = (uu___109_5915.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____5932  ->
                 match uu____5932 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___110_5944 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___110_5944.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___110_5944.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____5945 =
            FStar_List.fold_left
              (fun uu____5962  ->
                 fun uu____5963  ->
                   match (uu____5962, uu____5963) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____6013 = is_C c in
                       if uu____6013
                       then
                         let xw =
                           let uu____6021 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____6021 in
                         let x =
                           let uu___111_6023 = bv in
                           let uu____6024 =
                             let uu____6029 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____6029 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___111_6023.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___111_6023.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____6024
                           } in
                         let env3 =
                           let uu___112_6031 = env2 in
                           let uu____6032 =
                             let uu____6035 =
                               let uu____6036 =
                                 let uu____6045 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____6045) in
                               FStar_Syntax_Syntax.NT uu____6036 in
                             uu____6035 :: (env2.subst) in
                           {
                             env = (uu___112_6031.env);
                             subst = uu____6032;
                             tc_const = (uu___112_6031.tc_const)
                           } in
                         let uu____6046 =
                           let uu____6049 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____6050 =
                             let uu____6053 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____6053 :: acc in
                           uu____6049 :: uu____6050 in
                         (env3, uu____6046)
                       else
                         (let x =
                            let uu___113_6058 = bv in
                            let uu____6059 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___113_6058.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___113_6058.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____6059
                            } in
                          let uu____6064 =
                            let uu____6067 = FStar_Syntax_Syntax.mk_binder x in
                            uu____6067 :: acc in
                          (env2, uu____6064))) (env1, []) binders1 in
          (match uu____5945 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____6087 =
                 let check_what =
                   let uu____6105 = is_monadic what in
                   if uu____6105 then check_m else check_n in
                 let uu____6117 = check_what env2 body1 in
                 match uu____6117 with
                 | (t,s_body,u_body) ->
                     let uu____6133 =
                       let uu____6134 =
                         let uu____6135 = is_monadic what in
                         if uu____6135 then M t else N t in
                       comp_of_nm uu____6134 in
                     (uu____6133, s_body, u_body) in
               (match uu____6087 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
                          let uu____6213 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___95_6216  ->
                                    match uu___95_6216 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____6217 -> false)) in
                          if uu____6213
                          then
                            let double_starred_comp =
                              let uu____6231 =
                                let uu____6232 =
                                  let uu____6233 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____6233 in
                                FStar_All.pipe_left double_star uu____6232 in
                              FStar_Syntax_Syntax.mk_Total uu____6231 in
                            let flags =
                              FStar_List.filter
                                (fun uu___96_6241  ->
                                   match uu___96_6241 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____6242 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____6243 =
                              let uu____6254 =
                                let uu____6255 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____6255 in
                              FStar_Util.Inl uu____6254 in
                            FStar_Pervasives_Native.Some uu____6243
                          else
                            FStar_Pervasives_Native.Some
                              (FStar_Util.Inl
                                 ((let uu___114_6293 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___114_6293.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___114_6293.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___114_6293.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____6294  ->
                                          let c =
                                            lc.FStar_Syntax_Syntax.comp () in
                                          let result_typ =
                                            star_type' env2
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          FStar_Syntax_Util.set_result_typ c
                                            result_typ)
                                   })))
                      | FStar_Pervasives_Native.Some (FStar_Util.Inr
                          (lid,flags)) ->
                          let uu____6323 =
                            let uu____6334 =
                              let uu____6341 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___97_6344  ->
                                        match uu___97_6344 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____6345 -> false)) in
                              if uu____6341
                              then
                                let uu____6352 =
                                  FStar_List.filter
                                    (fun uu___98_6355  ->
                                       match uu___98_6355 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____6356 -> true) flags in
                                (FStar_Parser_Const.effect_Tot_lid,
                                  uu____6352)
                              else (lid, flags) in
                            FStar_Util.Inr uu____6334 in
                          FStar_Pervasives_Native.Some uu____6323 in
                    let uu____6378 =
                      let comp1 =
                        let uu____6400 = is_monadic what in
                        let uu____6401 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____6400 uu____6401 in
                      let uu____6402 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____6402,
                        (FStar_Pervasives_Native.Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____6378 with
                     | (u_body1,u_what) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           mk1
                             (FStar_Syntax_Syntax.Tm_abs
                                (s_binders1, s_body1, s_what)) in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           mk1
                             (FStar_Syntax_Syntax.Tm_abs
                                (u_binders2, u_body2, u_what)) in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.ty = uu____6548;
                FStar_Syntax_Syntax.p = uu____6549;_};
            FStar_Syntax_Syntax.fv_delta = uu____6550;
            FStar_Syntax_Syntax.fv_qual = uu____6551;_}
          ->
          let uu____6562 =
            let uu____6567 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6567 in
          (match uu____6562 with
           | (uu____6598,t) ->
               let uu____6600 = let uu____6601 = normalize1 t in N uu____6601 in
               (uu____6600, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6632 = check_n env head1 in
          (match uu____6632 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6652 =
                   let uu____6653 = FStar_Syntax_Subst.compress t in
                   uu____6653.FStar_Syntax_Syntax.n in
                 match uu____6652 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6658 -> true
                 | uu____6673 -> false in
               let rec flatten1 t =
                 let uu____6692 =
                   let uu____6693 = FStar_Syntax_Subst.compress t in
                   uu____6693.FStar_Syntax_Syntax.n in
                 match uu____6692 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6714);
                                FStar_Syntax_Syntax.tk = uu____6715;
                                FStar_Syntax_Syntax.pos = uu____6716;
                                FStar_Syntax_Syntax.vars = uu____6717;_})
                     when is_arrow t1 ->
                     let uu____6750 = flatten1 t1 in
                     (match uu____6750 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6848,uu____6849)
                     -> flatten1 e1
                 | uu____6906 ->
                     let uu____6907 =
                       let uu____6908 =
                         let uu____6909 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6909 in
                       FStar_Errors.Err uu____6908 in
                     raise uu____6907 in
               let uu____6924 = flatten1 t_head in
               (match uu____6924 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6994 =
                          let uu____6995 =
                            let uu____6996 = FStar_Util.string_of_int n1 in
                            let uu____7000 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____7006 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6996 uu____7000 uu____7006 in
                          FStar_Errors.Err uu____6995 in
                        raise uu____6994)
                     else ();
                     (let uu____7011 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____7011 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____7054 args1 =
                            match uu____7054 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____7136 =
                                       let uu____7137 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____7137.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____7136
                                 | (binders3,[]) ->
                                     let uu____7173 =
                                       let uu____7174 =
                                         let uu____7179 =
                                           let uu____7180 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____7180 in
                                         FStar_Syntax_Subst.compress
                                           uu____7179 in
                                       uu____7174.FStar_Syntax_Syntax.n in
                                     (match uu____7173 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____7209 =
                                            let uu____7210 =
                                              let uu____7211 =
                                                let uu____7226 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____7226) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____7211 in
                                            mk1 uu____7210 in
                                          N uu____7209
                                      | uu____7233 -> failwith "wat?")
                                 | ([],uu____7234::uu____7235) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____7283)::binders3,(arg,uu____7286)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____7351 = FStar_List.splitAt n' binders1 in
                          (match uu____7351 with
                           | (binders2,uu____7381) ->
                               let uu____7406 =
                                 let uu____7425 =
                                   FStar_List.map2
                                     (fun uu____7464  ->
                                        fun uu____7465  ->
                                          match (uu____7464, uu____7465) with
                                          | ((bv,uu____7497),(arg,q)) ->
                                              let uu____7508 =
                                                let uu____7509 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____7509.FStar_Syntax_Syntax.n in
                                              (match uu____7508 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7528 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____7552 ->
                                                   let uu____7553 =
                                                     check_n env arg in
                                                   (match uu____7553 with
                                                    | (uu____7574,s_arg,u_arg)
                                                        ->
                                                        let uu____7577 =
                                                          let uu____7584 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7584
                                                          then
                                                            let uu____7591 =
                                                              let uu____7596
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7596, q) in
                                                            [uu____7591;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7577))))
                                     binders2 args in
                                 FStar_List.split uu____7425 in
                               (match uu____7406 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7685 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7696 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7685, uu____7696)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7788) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7798) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7808,uu____7809) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7867 = let uu____7868 = env.tc_const c in N uu____7868 in
          (uu____7867, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7869 ->
          let uu____7884 =
            let uu____7885 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7885 in
          failwith uu____7884
      | FStar_Syntax_Syntax.Tm_type uu____7892 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7899 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7920 ->
          let uu____7929 =
            let uu____7930 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7930 in
          failwith uu____7929
      | FStar_Syntax_Syntax.Tm_uvar uu____7937 ->
          let uu____7954 =
            let uu____7955 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7955 in
          failwith uu____7954
      | FStar_Syntax_Syntax.Tm_delayed uu____7962 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____8007 =
            let uu____8008 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____8008 in
          failwith uu____8007
and mk_match:
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.withinfo_t,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                          FStar_Syntax_Syntax.syntax
                                          FStar_Pervasives_Native.option,
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos in
          let uu____8063 = check_n env e0 in
          match uu____8063 with
          | (uu____8076,s_e0,u_e0) ->
              let uu____8079 =
                let uu____8114 =
                  FStar_List.map
                    (fun b  ->
                       let uu____8178 = FStar_Syntax_Subst.open_branch b in
                       match uu____8178 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___115_8238 = env in
                             let uu____8239 =
                               let uu____8240 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____8240 in
                             {
                               env = uu____8239;
                               subst = (uu___115_8238.subst);
                               tc_const = (uu___115_8238.tc_const)
                             } in
                           let uu____8243 = f env1 body in
                           (match uu____8243 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8337 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____8114 in
              (match uu____8079 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8463 = FStar_List.hd nms in
                     match uu____8463 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___99_8467  ->
                          match uu___99_8467 with
                          | M uu____8468 -> true
                          | uu____8469 -> false) nms in
                   let uu____8470 =
                     let uu____8515 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8617  ->
                              match uu____8617 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8854 =
                                         check env original_body (M t2) in
                                       (match uu____8854 with
                                        | (uu____8899,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8954,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____8515 in
                   (match uu____8470 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____9185  ->
                                 match uu____9185 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____9262 =
                                         let uu____9263 =
                                           let uu____9282 =
                                             let uu____9289 =
                                               let uu____9294 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____9295 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____9294, uu____9295) in
                                             [uu____9289] in
                                           (s_body, uu____9282) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____9263 in
                                       mk1 uu____9262 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____9335 =
                              let uu____9336 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9336] in
                            let uu____9337 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____9340 =
                              let uu____9353 =
                                let uu____9364 =
                                  let uu____9365 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____9365 in
                                FStar_Util.Inl uu____9364 in
                              FStar_Pervasives_Native.Some uu____9353 in
                            FStar_Syntax_Util.abs uu____9335 uu____9337
                              uu____9340 in
                          let t1_star =
                            let uu____9391 =
                              let uu____9398 =
                                let uu____9399 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____9399 in
                              [uu____9398] in
                            let uu____9400 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____9391 uu____9400 in
                          let uu____9405 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____9464 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____9405, uu____9464)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____9487 =
                             let uu____9492 =
                               let uu____9493 =
                                 let uu____9528 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____9528,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____9493 in
                             mk1 uu____9492 in
                           let uu____9581 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____9487, uu____9581))))
and mk_let:
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
              FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos in
            let e1 = binding.FStar_Syntax_Syntax.lbdef in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname in
            let x_binders =
              let uu____9638 = FStar_Syntax_Syntax.mk_binder x in
              [uu____9638] in
            let uu____9639 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____9639 with
            | (x_binders1,e21) ->
                let uu____9652 = infer env e1 in
                (match uu____9652 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____9669 = is_C t1 in
                       if uu____9669
                       then
                         let uu___116_9670 = binding in
                         let uu____9671 =
                           let uu____9676 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____9676 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___116_9670.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___116_9670.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9671;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___116_9670.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___116_9670.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___117_9679 = env in
                       let uu____9680 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___118_9681 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___118_9681.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___118_9681.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9680;
                         subst = (uu___117_9679.subst);
                         tc_const = (uu___117_9679.tc_const)
                       } in
                     let uu____9682 = proceed env1 e21 in
                     (match uu____9682 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___119_9699 = binding in
                            let uu____9700 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___119_9699.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___119_9699.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9700;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___119_9699.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___119_9699.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____9705 =
                            let uu____9710 =
                              let uu____9711 =
                                let uu____9726 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___120_9735 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___120_9735.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___120_9735.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___120_9735.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___120_9735.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____9726) in
                              FStar_Syntax_Syntax.Tm_let uu____9711 in
                            mk1 uu____9710 in
                          let uu____9736 =
                            let uu____9741 =
                              let uu____9742 =
                                let uu____9757 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___121_9766 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_9766.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_9766.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_9766.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_9766.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9757) in
                              FStar_Syntax_Syntax.Tm_let uu____9742 in
                            mk1 uu____9741 in
                          (nm_rec, uu____9705, uu____9736))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___122_9779 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___122_9779.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___122_9779.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___122_9779.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___123_9781 = env in
                       let uu____9782 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___124_9783 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_9783.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_9783.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9782;
                         subst = (uu___123_9781.subst);
                         tc_const = (uu___123_9781.tc_const)
                       } in
                     let uu____9784 = ensure_m env1 e21 in
                     (match uu____9784 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____9811 =
                              let uu____9812 =
                                let uu____9831 =
                                  let uu____9838 =
                                    let uu____9843 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____9844 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9843, uu____9844) in
                                  [uu____9838] in
                                (s_e2, uu____9831) in
                              FStar_Syntax_Syntax.Tm_app uu____9812 in
                            mk1 uu____9811 in
                          let s_e22 =
                            let uu____9860 =
                              let uu____9873 =
                                let uu____9884 =
                                  let uu____9885 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____9885 in
                                FStar_Util.Inl uu____9884 in
                              FStar_Pervasives_Native.Some uu____9873 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____9860 in
                          let body =
                            let uu____9911 =
                              let uu____9912 =
                                let uu____9931 =
                                  let uu____9938 =
                                    let uu____9943 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____9943) in
                                  [uu____9938] in
                                (s_e1, uu____9931) in
                              FStar_Syntax_Syntax.Tm_app uu____9912 in
                            mk1 uu____9911 in
                          let uu____9958 =
                            let uu____9959 =
                              let uu____9960 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9960] in
                            let uu____9961 =
                              let uu____9974 =
                                let uu____9985 =
                                  let uu____9986 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____9986 in
                                FStar_Util.Inl uu____9985 in
                              FStar_Pervasives_Native.Some uu____9974 in
                            FStar_Syntax_Util.abs uu____9959 body uu____9961 in
                          let uu____10007 =
                            let uu____10012 =
                              let uu____10013 =
                                let uu____10028 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___125_10037 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_10037.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_10037.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_10037.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_10037.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____10028) in
                              FStar_Syntax_Syntax.Tm_let uu____10013 in
                            mk1 uu____10012 in
                          ((M t2), uu____9958, uu____10007)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10051 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____10051 in
      let uu____10052 = check env e mn in
      match uu____10052 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10068 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____10090 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____10090 in
      let uu____10091 = check env e mn in
      match uu____10091 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____10107 -> failwith "[check_m]: impossible"
and comp_of_nm: nm_ -> FStar_Syntax_Syntax.comp =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t
and mk_M: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp =
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
and type_of_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> FStar_Syntax_Util.comp_result t
and trans_F_:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____10141 =
           let uu____10142 = is_C c in Prims.op_Negation uu____10142 in
         if uu____10141 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____10152 =
           let uu____10153 = FStar_Syntax_Subst.compress c in
           uu____10153.FStar_Syntax_Syntax.n in
         match uu____10152 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____10188 = FStar_Syntax_Util.head_and_args wp in
             (match uu____10188 with
              | (wp_head,wp_args) ->
                  ((let uu____10238 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____10255 =
                           let uu____10256 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____10256 in
                         Prims.op_Negation uu____10255) in
                    if uu____10238 then failwith "mismatch" else ());
                   (let uu____10266 =
                      let uu____10267 =
                        let uu____10286 =
                          FStar_List.map2
                            (fun uu____10305  ->
                               fun uu____10306  ->
                                 match (uu____10305, uu____10306) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____10343 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____10343
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____10346 = print_implicit q in
                                         let uu____10347 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____10346 uu____10347)
                                      else ();
                                      (let uu____10349 =
                                         trans_F_ env arg wp_arg in
                                       (uu____10349, q)))) args wp_args in
                        (head1, uu____10286) in
                      FStar_Syntax_Syntax.Tm_app uu____10267 in
                    mk1 uu____10266)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____10389 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____10389 with
              | (binders_orig,comp1) ->
                  let uu____10396 =
                    let uu____10411 =
                      FStar_List.map
                        (fun uu____10438  ->
                           match uu____10438 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____10460 = is_C h in
                               if uu____10460
                               then
                                 let w' =
                                   let uu____10472 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____10472 in
                                 let uu____10473 =
                                   let uu____10480 =
                                     let uu____10487 =
                                       let uu____10492 =
                                         let uu____10493 =
                                           let uu____10494 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____10494 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____10493 in
                                       (uu____10492, q) in
                                     [uu____10487] in
                                   (w', q) :: uu____10480 in
                                 (w', uu____10473)
                               else
                                 (let x =
                                    let uu____10515 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____10515 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____10411 in
                  (match uu____10396 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____10570 =
                           let uu____10573 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____10573 in
                         FStar_Syntax_Subst.subst_comp uu____10570 comp1 in
                       let app =
                         let uu____10579 =
                           let uu____10580 =
                             let uu____10599 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____10611 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____10612 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____10611, uu____10612)) bvs in
                             (wp, uu____10599) in
                           FStar_Syntax_Syntax.Tm_app uu____10580 in
                         mk1 uu____10579 in
                       let comp3 =
                         let uu____10620 = type_of_comp comp2 in
                         let uu____10621 = is_monadic_comp comp2 in
                         trans_G env uu____10620 uu____10621 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____10623,uu____10624) ->
             trans_F_ env e wp
         | uu____10681 -> failwith "impossible trans_F_")
and trans_G:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____10686 =
              let uu____10687 = star_type' env h in
              let uu____10692 =
                let uu____10703 =
                  let uu____10708 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____10708) in
                [uu____10703] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____10687;
                FStar_Syntax_Syntax.effect_args = uu____10692;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____10686
          else
            (let uu____10718 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____10718)
let n:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.NoDeltaSteps;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
let star_type: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  -> let uu____10729 = n env.env t in star_type' env uu____10729
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____10746 = n env.env t in check_n env uu____10746
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____10756 = n env.env c in
        let uu____10757 = n env.env wp in
        trans_F_ env uu____10756 uu____10757