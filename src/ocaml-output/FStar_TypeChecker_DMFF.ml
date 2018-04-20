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
              let uu___78_93 = a in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___78_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___78_93.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____94
              } in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s in
            (let uu____102 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____102
             then
               (d "Elaborating extra WP combinators";
                (let uu____104 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____104))
             else ());
            (let rec collect_binders t =
               let uu____116 =
                 let uu____117 =
                   let uu____120 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____120 in
                 uu____117.FStar_Syntax_Syntax.n in
               match uu____116 with
               | FStar_Syntax_Syntax.Tm_arrow (bs, comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1, uu____151) -> t1
                     | uu____160 -> failwith "wp_a contains non-Tot arrow" in
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
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____245 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____245 with
                | (sigelt, fv) ->
                    ((let uu____253 =
                        let uu____256 = FStar_ST.op_Bang sigelts in sigelt ::
                          uu____256 in
                      FStar_ST.op_Colon_Equals sigelts uu____253);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____484 ->
                     match uu____484 with
                     | (t, b) ->
                         let uu____495 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____495)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t ->
                     let uu____526 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____526)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv ->
                     let uu____549 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____549) in
              let uu____550 =
                let uu____565 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____587 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____587 in
                    let uu____590 =
                      let uu____591 =
                        let uu____598 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____599 =
                          let uu____602 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____602] in
                        uu____598 :: uu____599 in
                      FStar_List.append binders uu____591 in
                    FStar_Syntax_Util.abs uu____590 body
                      FStar_Pervasives_Native.None in
                  let uu____607 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____608 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____607, uu____608) in
                match uu____565 with
                | (ctx_def, gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____642 =
                        let uu____643 =
                          let uu____658 =
                            let uu____665 =
                              FStar_List.map
                                (fun uu____685 ->
                                   match uu____685 with
                                   | (bv, uu____695) ->
                                       let uu____696 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____697 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____696, uu____697)) binders in
                            let uu____698 =
                              let uu____705 =
                                let uu____710 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____711 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____710, uu____711) in
                              let uu____712 =
                                let uu____719 =
                                  let uu____724 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____724) in
                                [uu____719] in
                              uu____705 :: uu____712 in
                            FStar_List.append uu____665 uu____698 in
                          (fv, uu____658) in
                        FStar_Syntax_Syntax.Tm_app uu____643 in
                      mk1 uu____642 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____550 with
              | (env1, mk_ctx, mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____783 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____783 in
                    let ret1 =
                      let uu____787 =
                        let uu____788 =
                          let uu____791 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____791 in
                        FStar_Syntax_Util.residual_tot uu____788 in
                      FStar_Pervasives_Native.Some uu____787 in
                    let body =
                      let uu____793 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____793 ret1 in
                    let uu____794 =
                      let uu____795 = mk_all_implicit binders in
                      let uu____802 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____795 uu____802 in
                    FStar_Syntax_Util.abs uu____794 body ret1 in
                  let c_pure1 =
                    let uu____830 = mk_lid "pure" in
                    register env1 uu____830 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____835 =
                        let uu____836 =
                          let uu____837 =
                            let uu____844 =
                              let uu____845 =
                                let uu____846 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____846 in
                              FStar_Syntax_Syntax.mk_binder uu____845 in
                            [uu____844] in
                          let uu____847 =
                            let uu____850 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____850 in
                          FStar_Syntax_Util.arrow uu____837 uu____847 in
                        mk_gctx uu____836 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____835 in
                    let r =
                      let uu____852 =
                        let uu____853 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____853 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____852 in
                    let ret1 =
                      let uu____857 =
                        let uu____858 =
                          let uu____861 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____861 in
                        FStar_Syntax_Util.residual_tot uu____858 in
                      FStar_Pervasives_Native.Some uu____857 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____869 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____872 =
                          let uu____881 =
                            let uu____884 =
                              let uu____885 =
                                let uu____886 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____886
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____885 in
                            [uu____884] in
                          FStar_List.append gamma_as_args uu____881 in
                        FStar_Syntax_Util.mk_app uu____869 uu____872 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____889 =
                      let uu____890 = mk_all_implicit binders in
                      let uu____897 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____890 uu____897 in
                    FStar_Syntax_Util.abs uu____889 outer_body ret1 in
                  let c_app1 =
                    let uu____933 = mk_lid "app" in
                    register env1 uu____933 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____940 =
                        let uu____947 =
                          let uu____948 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____948 in
                        [uu____947] in
                      let uu____949 =
                        let uu____952 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____952 in
                      FStar_Syntax_Util.arrow uu____940 uu____949 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____955 =
                        let uu____956 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____956 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____955 in
                    let ret1 =
                      let uu____960 =
                        let uu____961 =
                          let uu____964 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____964 in
                        FStar_Syntax_Util.residual_tot uu____961 in
                      FStar_Pervasives_Native.Some uu____960 in
                    let uu____965 =
                      let uu____966 = mk_all_implicit binders in
                      let uu____973 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____966 uu____973 in
                    let uu____1008 =
                      let uu____1009 =
                        let uu____1018 =
                          let uu____1021 =
                            let uu____1024 =
                              let uu____1033 =
                                let uu____1036 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____1036] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1033 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1024 in
                          let uu____1037 =
                            let uu____1042 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____1042] in
                          uu____1021 :: uu____1037 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1018 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1009 in
                    FStar_Syntax_Util.abs uu____965 uu____1008 ret1 in
                  let c_lift11 =
                    let uu____1046 = mk_lid "lift1" in
                    register env1 uu____1046 c_lift1 in
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
                      let uu____1054 =
                        let uu____1061 =
                          let uu____1062 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1062 in
                        let uu____1063 =
                          let uu____1066 =
                            let uu____1067 =
                              FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____1067 in
                          [uu____1066] in
                        uu____1061 :: uu____1063 in
                      let uu____1068 =
                        let uu____1071 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1071 in
                      FStar_Syntax_Util.arrow uu____1054 uu____1068 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1074 =
                        let uu____1075 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1075 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1074 in
                    let a2 =
                      let uu____1077 =
                        let uu____1078 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____1078 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1077 in
                    let ret1 =
                      let uu____1082 =
                        let uu____1083 =
                          let uu____1086 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____1086 in
                        FStar_Syntax_Util.residual_tot uu____1083 in
                      FStar_Pervasives_Native.Some uu____1082 in
                    let uu____1087 =
                      let uu____1088 = mk_all_implicit binders in
                      let uu____1095 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1088 uu____1095 in
                    let uu____1138 =
                      let uu____1139 =
                        let uu____1148 =
                          let uu____1151 =
                            let uu____1154 =
                              let uu____1163 =
                                let uu____1166 =
                                  let uu____1169 =
                                    let uu____1178 =
                                      let uu____1181 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1181] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1178 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1169 in
                                let uu____1182 =
                                  let uu____1187 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1187] in
                                uu____1166 :: uu____1182 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1163 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1154 in
                          let uu____1190 =
                            let uu____1195 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1195] in
                          uu____1151 :: uu____1190 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1148 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1139 in
                    FStar_Syntax_Util.abs uu____1087 uu____1138 ret1 in
                  let c_lift21 =
                    let uu____1199 = mk_lid "lift2" in
                    register env1 uu____1199 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1206 =
                        let uu____1213 =
                          let uu____1214 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1214 in
                        [uu____1213] in
                      let uu____1215 =
                        let uu____1218 =
                          let uu____1219 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1219 in
                        FStar_Syntax_Syntax.mk_Total uu____1218 in
                      FStar_Syntax_Util.arrow uu____1206 uu____1215 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1224 =
                        let uu____1225 =
                          let uu____1228 =
                            let uu____1229 =
                              let uu____1236 =
                                let uu____1237 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1237 in
                              [uu____1236] in
                            let uu____1238 =
                              let uu____1241 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1241 in
                            FStar_Syntax_Util.arrow uu____1229 uu____1238 in
                          mk_ctx uu____1228 in
                        FStar_Syntax_Util.residual_tot uu____1225 in
                      FStar_Pervasives_Native.Some uu____1224 in
                    let e1 =
                      let uu____1243 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1243 in
                    let body =
                      let uu____1245 =
                        let uu____1246 =
                          let uu____1253 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1253] in
                        FStar_List.append gamma uu____1246 in
                      let uu____1258 =
                        let uu____1259 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1262 =
                          let uu____1271 =
                            let uu____1272 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1272 in
                          let uu____1273 = args_of_binders1 gamma in
                          uu____1271 :: uu____1273 in
                        FStar_Syntax_Util.mk_app uu____1259 uu____1262 in
                      FStar_Syntax_Util.abs uu____1245 uu____1258 ret1 in
                    let uu____1276 =
                      let uu____1277 = mk_all_implicit binders in
                      let uu____1284 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1277 uu____1284 in
                    FStar_Syntax_Util.abs uu____1276 body ret1 in
                  let c_push1 =
                    let uu____1316 = mk_lid "push" in
                    register env1 uu____1316 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1336 =
                        let uu____1337 =
                          let uu____1352 = args_of_binders1 binders in
                          (c, uu____1352) in
                        FStar_Syntax_Syntax.Tm_app uu____1337 in
                      mk1 uu____1336
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1362 =
                        let uu____1363 =
                          let uu____1370 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1371 =
                            let uu____1374 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1374] in
                          uu____1370 :: uu____1371 in
                        let uu____1375 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1363 uu____1375 in
                      FStar_Syntax_Syntax.mk_Total uu____1362 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.kprop in
                    let uu____1379 =
                      let uu____1380 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1380 in
                    let uu____1391 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1393 =
                        let uu____1396 =
                          let uu____1405 =
                            let uu____1408 =
                              let uu____1411 =
                                let uu____1420 =
                                  let uu____1421 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1421 in
                                [uu____1420] in
                              FStar_Syntax_Util.mk_app l_ite uu____1411 in
                            [uu____1408] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1405 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1396 in
                      FStar_Syntax_Util.ascribe uu____1393
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1379 uu____1391
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1441 = mk_lid "wp_if_then_else" in
                    register env1 uu____1441 wp_if_then_else in
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
                      let uu____1452 =
                        let uu____1461 =
                          let uu____1464 =
                            let uu____1467 =
                              let uu____1476 =
                                let uu____1479 =
                                  let uu____1482 =
                                    let uu____1491 =
                                      let uu____1492 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1492 in
                                    [uu____1491] in
                                  FStar_Syntax_Util.mk_app l_and uu____1482 in
                                [uu____1479] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1476 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1467 in
                          let uu____1497 =
                            let uu____1502 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1502] in
                          uu____1464 :: uu____1497 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1461 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1452 in
                    let uu____1505 =
                      let uu____1506 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1506 in
                    FStar_Syntax_Util.abs uu____1505 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1518 = mk_lid "wp_assert" in
                    register env1 uu____1518 wp_assert in
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
                                  FStar_Syntax_Util.mk_app l_imp uu____1559 in
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
                  let wp_assume1 =
                    let uu____1595 = mk_lid "wp_assume" in
                    register env1 uu____1595 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1604 =
                        let uu____1611 =
                          let uu____1612 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1612 in
                        [uu____1611] in
                      let uu____1613 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1604 uu____1613 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1620 =
                        let uu____1629 =
                          let uu____1632 =
                            let uu____1635 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1635 in
                          let uu____1644 =
                            let uu____1649 =
                              let uu____1652 =
                                let uu____1661 =
                                  let uu____1664 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1664] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1661 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1652 in
                            [uu____1649] in
                          uu____1632 :: uu____1644 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1629 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1620 in
                    let uu____1671 =
                      let uu____1672 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1672 in
                    FStar_Syntax_Util.abs uu____1671 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1684 = mk_lid "wp_close" in
                    register env1 uu____1684 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1694 =
                      let uu____1695 =
                        let uu____1696 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1696 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1695 in
                    FStar_Pervasives_Native.Some uu____1694 in
                  let mk_forall1 x body =
                    let uu____1708 =
                      let uu____1711 =
                        let uu____1712 =
                          let uu____1727 =
                            let uu____1730 =
                              let uu____1731 =
                                let uu____1732 =
                                  let uu____1733 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1733] in
                                FStar_Syntax_Util.abs uu____1732 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1731 in
                            [uu____1730] in
                          (FStar_Syntax_Util.tforall, uu____1727) in
                        FStar_Syntax_Syntax.Tm_app uu____1712 in
                      FStar_Syntax_Syntax.mk uu____1711 in
                    uu____1708 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1743 =
                      let uu____1744 = FStar_Syntax_Subst.compress t in
                      uu____1744.FStar_Syntax_Syntax.n in
                    match uu____1743 with
                    | FStar_Syntax_Syntax.Tm_type uu____1747 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu____1773 ->
                              match uu____1773 with
                              | (b, uu____1779) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1780 -> true in
                  let rec is_monotonic t =
                    let uu____1785 =
                      let uu____1786 = FStar_Syntax_Subst.compress t in
                      uu____1786.FStar_Syntax_Syntax.n in
                    match uu____1785 with
                    | FStar_Syntax_Syntax.Tm_type uu____1789 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu____1815 ->
                              match uu____1815 with
                              | (b, uu____1821) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1822 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1874 =
                      let uu____1875 = FStar_Syntax_Subst.compress t1 in
                      uu____1875.FStar_Syntax_Syntax.n in
                    match uu____1874 with
                    | FStar_Syntax_Syntax.Tm_type uu____1878 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                             (b, uu____1881);
                           FStar_Syntax_Syntax.pos = uu____1882;
                           FStar_Syntax_Syntax.vars = uu____1883;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1917 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1917
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1920 =
                              let uu____1923 =
                                let uu____1932 =
                                  let uu____1933 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1933 in
                                [uu____1932] in
                              FStar_Syntax_Util.mk_app x uu____1923 in
                            let uu____1934 =
                              let uu____1937 =
                                let uu____1946 =
                                  let uu____1947 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1947 in
                                [uu____1946] in
                              FStar_Syntax_Util.mk_app y uu____1937 in
                            mk_rel1 b uu____1920 uu____1934 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1952 =
                               let uu____1953 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1956 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1953 uu____1956 in
                             let uu____1959 =
                               let uu____1960 =
                                 let uu____1963 =
                                   let uu____1972 =
                                     let uu____1973 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1973 in
                                   [uu____1972] in
                                 FStar_Syntax_Util.mk_app x uu____1963 in
                               let uu____1974 =
                                 let uu____1977 =
                                   let uu____1986 =
                                     let uu____1987 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1987 in
                                   [uu____1986] in
                                 FStar_Syntax_Util.mk_app y uu____1977 in
                               mk_rel1 b uu____1960 uu____1974 in
                             FStar_Syntax_Util.mk_imp uu____1952 uu____1959 in
                           let uu____1988 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1988)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                             (b, uu____1991);
                           FStar_Syntax_Syntax.pos = uu____1992;
                           FStar_Syntax_Syntax.vars = uu____1993;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2027 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2027
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2030 =
                              let uu____2033 =
                                let uu____2042 =
                                  let uu____2043 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2043 in
                                [uu____2042] in
                              FStar_Syntax_Util.mk_app x uu____2033 in
                            let uu____2044 =
                              let uu____2047 =
                                let uu____2056 =
                                  let uu____2057 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2057 in
                                [uu____2056] in
                              FStar_Syntax_Util.mk_app y uu____2047 in
                            mk_rel1 b uu____2030 uu____2044 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2062 =
                               let uu____2063 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2066 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2063 uu____2066 in
                             let uu____2069 =
                               let uu____2070 =
                                 let uu____2073 =
                                   let uu____2082 =
                                     let uu____2083 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2083 in
                                   [uu____2082] in
                                 FStar_Syntax_Util.mk_app x uu____2073 in
                               let uu____2084 =
                                 let uu____2087 =
                                   let uu____2096 =
                                     let uu____2097 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2097 in
                                   [uu____2096] in
                                 FStar_Syntax_Util.mk_app y uu____2087 in
                               mk_rel1 b uu____2070 uu____2084 in
                             FStar_Syntax_Util.mk_imp uu____2062 uu____2069 in
                           let uu____2098 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2098)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1, comp)
                        ->
                        let t2 =
                          let uu___79_2129 = t1 in
                          let uu____2130 =
                            let uu____2131 =
                              let uu____2144 =
                                let uu____2145 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2145 in
                              ([binder], uu____2144) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2131 in
                          {
                            FStar_Syntax_Syntax.n = uu____2130;
                            FStar_Syntax_Syntax.pos =
                              (uu___79_2129.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___79_2129.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2160 ->
                        failwith "unhandled arrow"
                    | uu____2173 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2188 =
                        let uu____2189 = FStar_Syntax_Subst.compress t1 in
                        uu____2189.FStar_Syntax_Syntax.n in
                      match uu____2188 with
                      | FStar_Syntax_Syntax.Tm_type uu____2192 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1, args) when
                          let uu____2215 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2215
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2230 =
                                let uu____2231 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2231 i in
                              FStar_Syntax_Syntax.fvar uu____2230
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2258 =
                            let uu____2265 =
                              FStar_List.mapi
                                (fun i ->
                                   fun uu____2279 ->
                                     match uu____2279 with
                                     | (t2, q) ->
                                         let uu____2286 = project i x in
                                         let uu____2287 = project i y in
                                         mk_stronger t2 uu____2286 uu____2287)
                                args in
                            match uu____2265 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2258 with
                           | (rel0, rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (b, uu____2314);
                             FStar_Syntax_Syntax.pos = uu____2315;
                             FStar_Syntax_Syntax.vars = uu____2316;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu____2354 ->
                                   match uu____2354 with
                                   | (bv, q) ->
                                       let uu____2361 =
                                         let uu____2362 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2362 in
                                       FStar_Syntax_Syntax.gen_bv uu____2361
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu____2369 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2369) bvs in
                          let body =
                            let uu____2371 = FStar_Syntax_Util.mk_app x args in
                            let uu____2372 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2371 uu____2372 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall1 bv body1) bvs
                            body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Total (b, uu____2379);
                             FStar_Syntax_Syntax.pos = uu____2380;
                             FStar_Syntax_Syntax.vars = uu____2381;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu____2419 ->
                                   match uu____2419 with
                                   | (bv, q) ->
                                       let uu____2426 =
                                         let uu____2427 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2427 in
                                       FStar_Syntax_Syntax.gen_bv uu____2426
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu____2434 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2434) bvs in
                          let body =
                            let uu____2436 = FStar_Syntax_Util.mk_app x args in
                            let uu____2437 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2436 uu____2437 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall1 bv body1) bvs
                            body
                      | uu____2442 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2444 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2445 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2446 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2444 uu____2445 uu____2446 in
                    let uu____2447 =
                      let uu____2448 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2448 in
                    FStar_Syntax_Util.abs uu____2447 body ret_tot_type in
                  let stronger1 =
                    let uu____2476 = mk_lid "stronger" in
                    register env1 uu____2476 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2482 = FStar_Util.prefix gamma in
                    match uu____2482 with
                    | (wp_args, post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2527 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2527 in
                          let uu____2530 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2530 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1, [], body))
                              ->
                              let k_app =
                                let uu____2540 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2540 in
                              let guard_free1 =
                                let uu____2550 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2550 in
                              let pat =
                                let uu____2554 =
                                  let uu____2563 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2563] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2554 in
                              let pattern_guarded_body =
                                let uu____2567 =
                                  let uu____2568 =
                                    let uu____2575 =
                                      let uu____2576 =
                                        let uu____2587 =
                                          let uu____2590 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2590] in
                                        [uu____2587] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2576 in
                                    (body, uu____2575) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2568 in
                                mk1 uu____2567 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2595 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2599 =
                            let uu____2600 =
                              let uu____2601 =
                                let uu____2602 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2605 =
                                  let uu____2614 = args_of_binders1 wp_args in
                                  let uu____2617 =
                                    let uu____2620 =
                                      let uu____2621 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2621 in
                                    [uu____2620] in
                                  FStar_List.append uu____2614 uu____2617 in
                                FStar_Syntax_Util.mk_app uu____2602
                                  uu____2605 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2601 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2600 in
                          FStar_Syntax_Util.abs gamma uu____2599
                            ret_gtot_type in
                        let uu____2622 =
                          let uu____2623 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2623 in
                        FStar_Syntax_Util.abs uu____2622 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2635 = mk_lid "wp_ite" in
                    register env1 uu____2635 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2641 = FStar_Util.prefix gamma in
                    match uu____2641 with
                    | (wp_args, post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2684 =
                            let uu____2685 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2688 =
                              let uu____2697 =
                                let uu____2698 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2698 in
                              [uu____2697] in
                            FStar_Syntax_Util.mk_app uu____2685 uu____2688 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2684 in
                        let uu____2699 =
                          let uu____2700 =
                            let uu____2707 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2707 gamma in
                          FStar_List.append binders uu____2700 in
                        FStar_Syntax_Util.abs uu____2699 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2723 = mk_lid "null_wp" in
                    register env1 uu____2723 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2732 =
                        let uu____2741 =
                          let uu____2744 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2745 =
                            let uu____2748 =
                              let uu____2751 =
                                let uu____2760 =
                                  let uu____2761 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2761 in
                                [uu____2760] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2751 in
                            let uu____2762 =
                              let uu____2767 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2767] in
                            uu____2748 :: uu____2762 in
                          uu____2744 :: uu____2745 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2741 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2732 in
                    let uu____2770 =
                      let uu____2771 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2771 in
                    FStar_Syntax_Util.abs uu____2770 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2783 = mk_lid "wp_trivial" in
                    register env1 uu____2783 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2788 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2788
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2793 =
                      let uu____2796 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____2796 in
                    let uu____2898 =
                      let uu___80_2899 = ed in
                      let uu____2900 =
                        let uu____2901 = c wp_if_then_else2 in
                        ([], uu____2901) in
                      let uu____2904 =
                        let uu____2905 = c wp_ite2 in ([], uu____2905) in
                      let uu____2908 =
                        let uu____2909 = c stronger2 in ([], uu____2909) in
                      let uu____2912 =
                        let uu____2913 = c wp_close2 in ([], uu____2913) in
                      let uu____2916 =
                        let uu____2917 = c wp_assert2 in ([], uu____2917) in
                      let uu____2920 =
                        let uu____2921 = c wp_assume2 in ([], uu____2921) in
                      let uu____2924 =
                        let uu____2925 = c null_wp2 in ([], uu____2925) in
                      let uu____2928 =
                        let uu____2929 = c wp_trivial2 in ([], uu____2929) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___80_2899.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___80_2899.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___80_2899.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___80_2899.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___80_2899.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___80_2899.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___80_2899.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2900;
                        FStar_Syntax_Syntax.ite_wp = uu____2904;
                        FStar_Syntax_Syntax.stronger = uu____2908;
                        FStar_Syntax_Syntax.close_wp = uu____2912;
                        FStar_Syntax_Syntax.assert_p = uu____2916;
                        FStar_Syntax_Syntax.assume_p = uu____2920;
                        FStar_Syntax_Syntax.null_wp = uu____2924;
                        FStar_Syntax_Syntax.trivial = uu____2928;
                        FStar_Syntax_Syntax.repr =
                          (uu___80_2899.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___80_2899.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___80_2899.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___80_2899.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___80_2899.FStar_Syntax_Syntax.eff_attrs)
                      } in
                    (uu____2793, uu____2898)))))
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env -> env.env
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env ->
    fun env' ->
      let uu___81_2943 = dmff_env in
      {
        env = env';
        subst = (uu___81_2943.subst);
        tc_const = (uu___81_2943.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee -> match projectee with | N _0 -> true | uu____2956 -> false
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | N _0 -> _0
let (uu___is_M : nm -> Prims.bool) =
  fun projectee -> match projectee with | M _0 -> true | uu____2968 -> false
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | M _0 -> _0
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___67_2978 ->
    match uu___67_2978 with
    | FStar_Syntax_Syntax.Total (t, uu____2980) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___66_2993 ->
                match uu___66_2993 with
                | FStar_Syntax_Syntax.CPS -> true
                | uu____2994 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2996 =
          let uu____2997 =
            let uu____2998 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2998 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2997 in
        failwith uu____2996
    | FStar_Syntax_Syntax.GTotal uu____2999 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let (string_of_nm : nm -> Prims.string) =
  fun uu___68_3010 ->
    match uu___68_3010 with
    | N t ->
        let uu____3012 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____3012
    | M t ->
        let uu____3014 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____3014
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1 ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3018,
         { FStar_Syntax_Syntax.n = n2; FStar_Syntax_Syntax.pos = uu____3020;
           FStar_Syntax_Syntax.vars = uu____3021;_})
        -> nm_of_comp n2
    | uu____3038 -> failwith "unexpected_argument: [is_monadic_arrow]"
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    let uu____3046 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____3046 with | M uu____3047 -> true | N uu____3048 -> false
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Not_found -> true | uu____3052 -> false
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ ->
    let star_once typ1 =
      let uu____3062 =
        let uu____3069 =
          let uu____3070 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3070 in
        [uu____3069] in
      let uu____3071 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.kprop in
      FStar_Syntax_Util.arrow uu____3062 uu____3071 in
    let uu____3074 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____3074
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
        mk1
          (let uu____3111 =
             let uu____3124 =
               let uu____3131 =
                 let uu____3136 =
                   let uu____3137 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____3137 in
                 let uu____3138 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____3136, uu____3138) in
               [uu____3131] in
             let uu____3147 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.kprop in
             (uu____3124, uu____3147) in
           FStar_Syntax_Syntax.Tm_arrow uu____3111)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders, uu____3175) ->
          let binders1 =
            FStar_List.map
              (fun uu____3211 ->
                 match uu____3211 with
                 | (bv, aqual) ->
                     let uu____3222 =
                       let uu___82_3223 = bv in
                       let uu____3224 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___82_3223.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___82_3223.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3224
                       } in
                     (uu____3222, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3227,
                {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                    (hn, uu____3229);
                  FStar_Syntax_Syntax.pos = uu____3230;
                  FStar_Syntax_Syntax.vars = uu____3231;_})
               ->
               let uu____3256 =
                 let uu____3257 =
                   let uu____3270 =
                     let uu____3271 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3271 in
                   (binders1, uu____3270) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3257 in
               mk1 uu____3256
           | uu____3278 ->
               let uu____3279 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3279 with
                | N hn ->
                    let uu____3281 =
                      let uu____3282 =
                        let uu____3295 =
                          let uu____3296 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3296 in
                        (binders1, uu____3295) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3282 in
                    mk1 uu____3281
                | M a ->
                    let uu____3304 =
                      let uu____3305 =
                        let uu____3318 =
                          let uu____3325 =
                            let uu____3332 =
                              let uu____3337 =
                                let uu____3338 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3338 in
                              let uu____3339 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3337, uu____3339) in
                            [uu____3332] in
                          FStar_List.append binders1 uu____3325 in
                        let uu____3352 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.kprop in
                        (uu____3318, uu____3352) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3305 in
                    mk1 uu____3304))
      | FStar_Syntax_Syntax.Tm_app (head1, args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3422 = f x in
                    FStar_Util.string_builder_append strb uu____3422);
                   FStar_List.iter
                     (fun x1 ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3429 = f x1 in
                         FStar_Util.string_builder_append strb uu____3429))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3431 =
              let uu____3436 =
                let uu____3437 = FStar_Syntax_Print.term_to_string t2 in
                let uu____3438 =
                  string_of_set FStar_Syntax_Print.bv_to_string s in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3437 uu____3438 in
              (FStar_Errors.Warning_DependencyFound, uu____3436) in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3431 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3446 =
              let uu____3447 = FStar_Syntax_Subst.compress ty in
              uu____3447.FStar_Syntax_Syntax.n in
            match uu____3446 with
            | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
                let uu____3468 =
                  let uu____3469 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3469 in
                if uu____3468
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3495 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3495 s in
                       let uu____3498 =
                         let uu____3499 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3499 in
                       if uu____3498
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else () in
                     let uu____3502 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3502 with
                     | (binders1, c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s ->
                                fun uu____3524 ->
                                  match uu____3524 with
                                  | (bv, uu____3534) ->
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
            | uu____3548 ->
                ((let uu____3550 =
                    let uu____3555 =
                      let uu____3556 = FStar_Syntax_Print.term_to_string ty in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3556 in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3555) in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3550);
                 false) in
          let rec is_valid_application head2 =
            let uu____3561 =
              let uu____3562 = FStar_Syntax_Subst.compress head2 in
              uu____3562.FStar_Syntax_Syntax.n in
            match uu____3561 with
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
                  (let uu____3567 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3567)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3569 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3569 with
                 | ((uu____3578, ty), uu____3580) ->
                     let uu____3585 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3585
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       let uu____3593 =
                         let uu____3594 = FStar_Syntax_Subst.compress res in
                         uu____3594.FStar_Syntax_Syntax.n in
                       (match uu____3593 with
                        | FStar_Syntax_Syntax.Tm_app uu____3597 -> true
                        | uu____3612 ->
                            ((let uu____3614 =
                                let uu____3619 =
                                  let uu____3620 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3620 in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3619) in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3614);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3622 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3623 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2, uu____3625) ->
                is_valid_application t2
            | uu____3630 -> false in
          let uu____3631 = is_valid_application head1 in
          if uu____3631
          then
            let uu____3632 =
              let uu____3633 =
                let uu____3648 =
                  FStar_List.map
                    (fun uu____3669 ->
                       match uu____3669 with
                       | (t2, qual) ->
                           let uu____3686 = star_type' env t2 in
                           (uu____3686, qual)) args in
                (head1, uu____3648) in
              FStar_Syntax_Syntax.Tm_app uu____3633 in
            mk1 uu____3632
          else
            (let uu____3696 =
               let uu____3701 =
                 let uu____3702 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3702 in
               (FStar_Errors.Fatal_WrongTerm, uu____3701) in
             FStar_Errors.raise_err uu____3696)
      | FStar_Syntax_Syntax.Tm_bvar uu____3703 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3704 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3705 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3706 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders, repr, something) ->
          let uu____3730 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3730 with
           | (binders1, repr1) ->
               let env1 =
                 let uu___85_3738 = env in
                 let uu____3739 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3739;
                   subst = (uu___85_3738.subst);
                   tc_const = (uu___85_3738.tc_const)
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
               ((let uu___86_3759 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___86_3759.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___86_3759.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2, m) ->
          let uu____3766 =
            let uu____3767 =
              let uu____3774 = star_type' env t2 in (uu____3774, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3767 in
          mk1 uu____3766
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Util.Inl t2, FStar_Pervasives_Native.None), something)
          ->
          let uu____3822 =
            let uu____3823 =
              let uu____3850 = star_type' env e in
              let uu____3851 =
                let uu____3866 =
                  let uu____3873 = star_type' env t2 in
                  FStar_Util.Inl uu____3873 in
                (uu____3866, FStar_Pervasives_Native.None) in
              (uu____3850, uu____3851, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3823 in
          mk1 uu____3822
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Util.Inr c, FStar_Pervasives_Native.None), something) ->
          let uu____3951 =
            let uu____3952 =
              let uu____3979 = star_type' env e in
              let uu____3980 =
                let uu____3995 =
                  let uu____4002 =
                    star_type' env (FStar_Syntax_Util.comp_result c) in
                  FStar_Util.Inl uu____4002 in
                (uu____3995, FStar_Pervasives_Native.None) in
              (uu____3979, uu____3980, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3952 in
          mk1 uu____3951
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4033, (uu____4034, FStar_Pervasives_Native.Some uu____4035),
           uu____4036)
          ->
          let uu____4085 =
            let uu____4090 =
              let uu____4091 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4091 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4090) in
          FStar_Errors.raise_err uu____4085
      | FStar_Syntax_Syntax.Tm_refine uu____4092 ->
          let uu____4099 =
            let uu____4104 =
              let uu____4105 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4105 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4104) in
          FStar_Errors.raise_err uu____4099
      | FStar_Syntax_Syntax.Tm_uinst uu____4106 ->
          let uu____4113 =
            let uu____4118 =
              let uu____4119 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4119 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4118) in
          FStar_Errors.raise_err uu____4113
      | FStar_Syntax_Syntax.Tm_quoted uu____4120 ->
          let uu____4127 =
            let uu____4132 =
              let uu____4133 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4133 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4132) in
          FStar_Errors.raise_err uu____4127
      | FStar_Syntax_Syntax.Tm_constant uu____4134 ->
          let uu____4135 =
            let uu____4140 =
              let uu____4141 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4141 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4140) in
          FStar_Errors.raise_err uu____4135
      | FStar_Syntax_Syntax.Tm_match uu____4142 ->
          let uu____4165 =
            let uu____4170 =
              let uu____4171 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4171 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4170) in
          FStar_Errors.raise_err uu____4165
      | FStar_Syntax_Syntax.Tm_let uu____4172 ->
          let uu____4185 =
            let uu____4190 =
              let uu____4191 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4191 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4190) in
          FStar_Errors.raise_err uu____4185
      | FStar_Syntax_Syntax.Tm_uvar uu____4192 ->
          let uu____4209 =
            let uu____4214 =
              let uu____4215 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4215 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4214) in
          FStar_Errors.raise_err uu____4209
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____4216 =
            let uu____4221 =
              let uu____4222 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4222 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4221) in
          FStar_Errors.raise_err uu____4216
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4224 = FStar_Syntax_Util.unfold_lazy i in
          star_type' env uu____4224
      | FStar_Syntax_Syntax.Tm_delayed uu____4227 -> failwith "impossible"
let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___70_4256 ->
    match uu___70_4256 with
    | FStar_Pervasives_Native.None -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___69_4263 ->
                match uu___69_4263 with
                | FStar_Syntax_Syntax.CPS -> true
                | uu____4264 -> false))
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    let uu____4268 =
      let uu____4269 = FStar_Syntax_Subst.compress t in
      uu____4269.FStar_Syntax_Syntax.n in
    match uu____4268 with
    | FStar_Syntax_Syntax.Tm_app (head1, args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4295 =
            let uu____4296 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____4296 in
          is_C uu____4295 in
        if r
        then
          ((let uu____4312 =
              let uu____4313 =
                FStar_List.for_all
                  (fun uu____4321 ->
                     match uu____4321 with | (h, uu____4327) -> is_C h) args in
              Prims.op_Negation uu____4313 in
            if uu____4312 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4331 =
              let uu____4332 =
                FStar_List.for_all
                  (fun uu____4341 ->
                     match uu____4341 with
                     | (h, uu____4347) ->
                         let uu____4348 = is_C h in
                         Prims.op_Negation uu____4348) args in
              Prims.op_Negation uu____4332 in
            if uu____4331 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
        let uu____4368 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4368 with
         | M t1 ->
             ((let uu____4371 = is_C t1 in
               if uu____4371 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____4375) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu____4381) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____4387, uu____4388) -> is_C t1
    | uu____4429 -> false
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
          let uu____4452 =
            let uu____4453 =
              let uu____4468 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4469 =
                let uu____4476 =
                  let uu____4481 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4481) in
                [uu____4476] in
              (uu____4468, uu____4469) in
            FStar_Syntax_Syntax.Tm_app uu____4453 in
          mk1 uu____4452 in
        let uu____4496 =
          let uu____4497 = FStar_Syntax_Syntax.mk_binder p in [uu____4497] in
        FStar_Syntax_Util.abs uu____4496 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.kprop))
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___71_4500 ->
    match uu___71_4500 with
    | FStar_Syntax_Syntax.Tm_unknown -> true
    | uu____4501 -> false
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
        let return_if uu____4676 =
          match uu____4676 with
          | (rec_nm, s_e, u_e) ->
              let check1 t1 t2 =
                let uu____4703 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4705 =
                       let uu____4706 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4706 in
                     Prims.op_Negation uu____4705) in
                if uu____4703
                then
                  let uu____4707 =
                    let uu____4712 =
                      let uu____4713 = FStar_Syntax_Print.term_to_string e in
                      let uu____4714 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4715 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4713 uu____4714 uu____4715 in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4712) in
                  FStar_Errors.raise_err uu____4707
                else () in
              (match (rec_nm, context_nm) with
               | (N t1, N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1, M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1, M t2) ->
                   (check1 t1 t2;
                    (let uu____4732 = mk_return env t1 s_e in
                     ((M t1), uu____4732, u_e)))
               | (M t1, N t2) ->
                   let uu____4735 =
                     let uu____4740 =
                       let uu____4741 = FStar_Syntax_Print.term_to_string e in
                       let uu____4742 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4743 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4741 uu____4742 uu____4743 in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4740) in
                   FStar_Errors.raise_err uu____4735) in
        let ensure_m env1 e2 =
          let strip_m uu___72_4784 =
            match uu___72_4784 with
            | (M t, s_e, u_e) -> (t, s_e, u_e)
            | uu____4800 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4820 =
                let uu____4825 =
                  let uu____4826 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4826 in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4825) in
              FStar_Errors.raise_error uu____4820 e2.FStar_Syntax_Syntax.pos
          | M uu____4833 ->
              let uu____4834 = check env1 e2 context_nm in strip_m uu____4834 in
        let uu____4841 =
          let uu____4842 = FStar_Syntax_Subst.compress e in
          uu____4842.FStar_Syntax_Syntax.n in
        match uu____4841 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4851 ->
            let uu____4852 = infer env e in return_if uu____4852
        | FStar_Syntax_Syntax.Tm_name uu____4859 ->
            let uu____4860 = infer env e in return_if uu____4860
        | FStar_Syntax_Syntax.Tm_fvar uu____4867 ->
            let uu____4868 = infer env e in return_if uu____4868
        | FStar_Syntax_Syntax.Tm_abs uu____4875 ->
            let uu____4892 = infer env e in return_if uu____4892
        | FStar_Syntax_Syntax.Tm_constant uu____4899 ->
            let uu____4900 = infer env e in return_if uu____4900
        | FStar_Syntax_Syntax.Tm_quoted uu____4907 ->
            let uu____4914 = infer env e in return_if uu____4914
        | FStar_Syntax_Syntax.Tm_app uu____4921 ->
            let uu____4936 = infer env e in return_if uu____4936
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____4944 = FStar_Syntax_Util.unfold_lazy i in
            check env uu____4944 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
            mk_let env binding e2
              (fun env1 -> fun e21 -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0, branches) ->
            mk_match env e0 branches
              (fun env1 -> fun body -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1, uu____5006) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1, uu____5012) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1, uu____5018, uu____5019) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5060 ->
            let uu____5073 =
              let uu____5074 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5074 in
            failwith uu____5073
        | FStar_Syntax_Syntax.Tm_type uu____5081 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5088 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5107 ->
            let uu____5114 =
              let uu____5115 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5115 in
            failwith uu____5114
        | FStar_Syntax_Syntax.Tm_uvar uu____5122 ->
            let uu____5139 =
              let uu____5140 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5140 in
            failwith uu____5139
        | FStar_Syntax_Syntax.Tm_delayed uu____5147 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu____5178 =
              let uu____5179 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5179 in
            failwith uu____5178
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
      let uu____5203 =
        let uu____5204 = FStar_Syntax_Subst.compress e in
        uu____5204.FStar_Syntax_Syntax.n in
      match uu____5203 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5222 = FStar_Syntax_Util.unfold_lazy i in
          infer env uu____5222
      | FStar_Syntax_Syntax.Tm_abs (binders, body, rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5265;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None;
                  FStar_Syntax_Syntax.residual_flags = uu____5266;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5272 =
                  let uu___87_5273 = rc in
                  let uu____5274 =
                    let uu____5279 =
                      let uu____5280 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____5280 in
                    FStar_Pervasives_Native.Some uu____5279 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___87_5273.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5274;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___87_5273.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____5272 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___88_5290 = env in
            let uu____5291 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____5291;
              subst = (uu___88_5290.subst);
              tc_const = (uu___88_5290.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____5311 ->
                 match uu____5311 with
                 | (bv, qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___89_5324 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___89_5324.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___89_5324.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____5325 =
            FStar_List.fold_left
              (fun uu____5354 ->
                 fun uu____5355 ->
                   match (uu____5354, uu____5355) with
                   | ((env2, acc), (bv, qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5403 = is_C c in
                       if uu____5403
                       then
                         let xw =
                           let uu____5411 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5411 in
                         let x =
                           let uu___90_5413 = bv in
                           let uu____5414 =
                             let uu____5417 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5417 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___90_5413.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___90_5413.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5414
                           } in
                         let env3 =
                           let uu___91_5419 = env2 in
                           let uu____5420 =
                             let uu____5423 =
                               let uu____5424 =
                                 let uu____5431 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5431) in
                               FStar_Syntax_Syntax.NT uu____5424 in
                             uu____5423 :: (env2.subst) in
                           {
                             env = (uu___91_5419.env);
                             subst = uu____5420;
                             tc_const = (uu___91_5419.tc_const)
                           } in
                         let uu____5432 =
                           let uu____5435 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5436 =
                             let uu____5439 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5439 :: acc in
                           uu____5435 :: uu____5436 in
                         (env3, uu____5432)
                       else
                         (let x =
                            let uu___92_5444 = bv in
                            let uu____5445 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___92_5444.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___92_5444.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5445
                            } in
                          let uu____5448 =
                            let uu____5451 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5451 :: acc in
                          (env2, uu____5448))) (env1, []) binders1 in
          (match uu____5325 with
           | (env2, u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5471 =
                 let check_what =
                   let uu____5489 = is_monadic rc_opt1 in
                   if uu____5489 then check_m else check_n in
                 let uu____5501 = check_what env2 body1 in
                 match uu____5501 with
                 | (t, s_body, u_body) ->
                     let uu____5517 =
                       let uu____5518 =
                         let uu____5519 = is_monadic rc_opt1 in
                         if uu____5519 then M t else N t in
                       comp_of_nm uu____5518 in
                     (uu____5517, s_body, u_body) in
               (match uu____5471 with
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
                                 let uu____5544 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___73_5548 ->
                                           match uu___73_5548 with
                                           | FStar_Syntax_Syntax.CPS -> true
                                           | uu____5549 -> false)) in
                                 if uu____5544
                                 then
                                   let uu____5550 =
                                     FStar_List.filter
                                       (fun uu___74_5554 ->
                                          match uu___74_5554 with
                                          | FStar_Syntax_Syntax.CPS -> false
                                          | uu____5555 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5550
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5564 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___75_5568 ->
                                         match uu___75_5568 with
                                         | FStar_Syntax_Syntax.CPS -> true
                                         | uu____5569 -> false)) in
                               if uu____5564
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___76_5576 ->
                                        match uu___76_5576 with
                                        | FStar_Syntax_Syntax.CPS -> false
                                        | uu____5577 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5578 =
                                   let uu____5579 =
                                     let uu____5584 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5584 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5579 flags1 in
                                 FStar_Pervasives_Native.Some uu____5578
                               else
                                 (let uu____5586 =
                                    let uu___93_5587 = rc in
                                    let uu____5588 =
                                      let uu____5593 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5593 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___93_5587.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5588;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___93_5587.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5586)) in
                    let uu____5594 =
                      let comp1 =
                        let uu____5604 = is_monadic rc_opt1 in
                        let uu____5605 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5604 uu____5605 in
                      let uu____5606 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5606,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5594 with
                     | (u_body1, u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5648 =
                             let uu____5649 =
                               let uu____5666 =
                                 let uu____5669 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5669 s_rc_opt in
                               (s_binders1, s_body1, uu____5666) in
                             FStar_Syntax_Syntax.Tm_abs uu____5649 in
                           mk1 uu____5648 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5679 =
                             let uu____5680 =
                               let uu____5697 =
                                 let uu____5700 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5700 u_rc_opt in
                               (u_binders2, u_body2, uu____5697) in
                             FStar_Syntax_Syntax.Tm_abs uu____5680 in
                           mk1 uu____5679 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5710;_};
            FStar_Syntax_Syntax.fv_delta = uu____5711;
            FStar_Syntax_Syntax.fv_qual = uu____5712;_}
          ->
          let uu____5715 =
            let uu____5720 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5720 in
          (match uu____5715 with
           | (uu____5751, t) ->
               let uu____5753 = let uu____5754 = normalize1 t in N uu____5754 in
               (uu____5753, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____5755;
             FStar_Syntax_Syntax.vars = uu____5756;_},
           a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5819 = FStar_Syntax_Util.head_and_args e in
          (match uu____5819 with
           | (unary_op, uu____5841) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____5900;
             FStar_Syntax_Syntax.vars = uu____5901;_},
           a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5977 = FStar_Syntax_Util.head_and_args e in
          (match uu____5977 with
           | (unary_op, uu____5999) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____6064;
             FStar_Syntax_Syntax.vars = uu____6065;_},
           (a, FStar_Pervasives_Native.None)::[])
          ->
          let uu____6103 = infer env a in
          (match uu____6103 with
           | (t, s, u) ->
               let uu____6119 = FStar_Syntax_Util.head_and_args e in
               (match uu____6119 with
                | (head1, uu____6141) ->
                    let uu____6162 =
                      let uu____6163 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____6163 in
                    let uu____6164 =
                      let uu____6167 =
                        let uu____6168 =
                          let uu____6183 =
                            let uu____6186 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6186] in
                          (head1, uu____6183) in
                        FStar_Syntax_Syntax.Tm_app uu____6168 in
                      mk1 uu____6167 in
                    let uu____6191 =
                      let uu____6194 =
                        let uu____6195 =
                          let uu____6210 =
                            let uu____6213 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6213] in
                          (head1, uu____6210) in
                        FStar_Syntax_Syntax.Tm_app uu____6195 in
                      mk1 uu____6194 in
                    (uu____6162, uu____6164, uu____6191)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____6222;
             FStar_Syntax_Syntax.vars = uu____6223;_},
           (a1, uu____6225)::a2::[])
          ->
          let uu____6267 = infer env a1 in
          (match uu____6267 with
           | (t, s, u) ->
               let uu____6283 = FStar_Syntax_Util.head_and_args e in
               (match uu____6283 with
                | (head1, uu____6305) ->
                    let uu____6326 =
                      let uu____6329 =
                        let uu____6330 =
                          let uu____6345 =
                            let uu____6348 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6348; a2] in
                          (head1, uu____6345) in
                        FStar_Syntax_Syntax.Tm_app uu____6330 in
                      mk1 uu____6329 in
                    let uu____6365 =
                      let uu____6368 =
                        let uu____6369 =
                          let uu____6384 =
                            let uu____6387 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6387; a2] in
                          (head1, uu____6384) in
                        FStar_Syntax_Syntax.Tm_app uu____6369 in
                      mk1 uu____6368 in
                    (t, uu____6326, uu____6365)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu____6408;
             FStar_Syntax_Syntax.vars = uu____6409;_},
           uu____6410)
          ->
          let uu____6431 =
            let uu____6436 =
              let uu____6437 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6437 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6436) in
          FStar_Errors.raise_error uu____6431 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu____6444;
             FStar_Syntax_Syntax.vars = uu____6445;_},
           uu____6446)
          ->
          let uu____6467 =
            let uu____6472 =
              let uu____6473 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6473 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6472) in
          FStar_Errors.raise_error uu____6467 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1, args) ->
          let uu____6502 = check_n env head1 in
          (match uu____6502 with
           | (t_head, s_head, u_head) ->
               let is_arrow t =
                 let uu____6522 =
                   let uu____6523 = FStar_Syntax_Subst.compress t in
                   uu____6523.FStar_Syntax_Syntax.n in
                 match uu____6522 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6526 -> true
                 | uu____6539 -> false in
               let rec flatten1 t =
                 let uu____6556 =
                   let uu____6557 = FStar_Syntax_Subst.compress t in
                   uu____6557.FStar_Syntax_Syntax.n in
                 match uu____6556 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,
                      {
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                          (t1, uu____6574);
                        FStar_Syntax_Syntax.pos = uu____6575;
                        FStar_Syntax_Syntax.vars = uu____6576;_})
                     when is_arrow t1 ->
                     let uu____6601 = flatten1 t1 in
                     (match uu____6601 with
                      | (binders', comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1, uu____6683, uu____6684) -> flatten1 e1
                 | uu____6725 ->
                     let uu____6726 =
                       let uu____6731 =
                         let uu____6732 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6732 in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6731) in
                     FStar_Errors.raise_err uu____6726 in
               let uu____6745 = flatten1 t_head in
               (match uu____6745 with
                | (binders, comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6805 =
                          let uu____6810 =
                            let uu____6811 = FStar_Util.string_of_int n1 in
                            let uu____6818 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____6829 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6811 uu____6818 uu____6829 in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6810) in
                        FStar_Errors.raise_err uu____6805)
                     else ();
                     (let uu____6837 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____6837 with
                      | (binders1, comp1) ->
                          let rec final_type subst1 uu____6878 args1 =
                            match uu____6878 with
                            | (binders2, comp2) ->
                                (match (binders2, args1) with
                                 | ([], []) ->
                                     let uu____6952 =
                                       let uu____6953 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____6953.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____6952
                                 | (binders3, []) ->
                                     let uu____6983 =
                                       let uu____6984 =
                                         let uu____6987 =
                                           let uu____6988 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6988 in
                                         FStar_Syntax_Subst.compress
                                           uu____6987 in
                                       uu____6984.FStar_Syntax_Syntax.n in
                                     (match uu____6983 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4, comp3) ->
                                          let uu____7013 =
                                            let uu____7014 =
                                              let uu____7015 =
                                                let uu____7028 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____7028) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____7015 in
                                            mk1 uu____7014 in
                                          N uu____7013
                                      | uu____7035 -> failwith "wat?")
                                 | ([], uu____7036::uu____7037) ->
                                     failwith "just checked that?!"
                                 | ((bv, uu____7077)::binders3,
                                    (arg, uu____7080)::args2) ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____7133 = FStar_List.splitAt n' binders1 in
                          (match uu____7133 with
                           | (binders2, uu____7165) ->
                               let uu____7190 =
                                 let uu____7211 =
                                   FStar_List.map2
                                     (fun uu____7265 ->
                                        fun uu____7266 ->
                                          match (uu____7265, uu____7266) with
                                          | ((bv, uu____7304), (arg, q)) ->
                                              let uu____7321 =
                                                let uu____7322 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____7322.FStar_Syntax_Syntax.n in
                                              (match uu____7321 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7341 ->
                                                   let uu____7342 =
                                                     let uu____7347 =
                                                       star_type' env arg in
                                                     (uu____7347, q) in
                                                   (uu____7342, [(arg, q)])
                                               | uu____7374 ->
                                                   let uu____7375 =
                                                     check_n env arg in
                                                   (match uu____7375 with
                                                    | (uu____7398, s_arg,
                                                       u_arg) ->
                                                        let uu____7401 =
                                                          let uu____7408 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7408
                                                          then
                                                            let uu____7415 =
                                                              let uu____7420
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7420, q) in
                                                            [uu____7415;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7401))))
                                     binders2 args in
                                 FStar_List.split uu____7211 in
                               (match uu____7190 with
                                | (s_args, u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7519 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7528 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7519, uu____7528)))))))
      | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0, branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1, uu____7596) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1, uu____7602) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1, uu____7608, uu____7609) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7651 = let uu____7652 = env.tc_const c in N uu____7652 in
          (uu____7651, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm, qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7659 ->
          let uu____7672 =
            let uu____7673 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7673 in
          failwith uu____7672
      | FStar_Syntax_Syntax.Tm_type uu____7680 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7687 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7706 ->
          let uu____7713 =
            let uu____7714 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7714 in
          failwith uu____7713
      | FStar_Syntax_Syntax.Tm_uvar uu____7721 ->
          let uu____7738 =
            let uu____7739 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7739 in
          failwith uu____7738
      | FStar_Syntax_Syntax.Tm_delayed uu____7746 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu____7777 =
            let uu____7778 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7778 in
          failwith uu____7777
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
          let uu____7823 = check_n env e0 in
          match uu____7823 with
          | (uu____7836, s_e0, u_e0) ->
              let uu____7839 =
                let uu____7868 =
                  FStar_List.map
                    (fun b ->
                       let uu____7929 = FStar_Syntax_Subst.open_branch b in
                       match uu____7929 with
                       | (pat, FStar_Pervasives_Native.None, body) ->
                           let env1 =
                             let uu___94_7971 = env in
                             let uu____7972 =
                               let uu____7973 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7973 in
                             {
                               env = uu____7972;
                               subst = (uu___94_7971.subst);
                               tc_const = (uu___94_7971.tc_const)
                             } in
                           let uu____7976 = f env1 body in
                           (match uu____7976 with
                            | (nm, s_body, u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8048 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____7868 in
              (match uu____7839 with
               | (nms, branches1) ->
                   let t1 =
                     let uu____8150 = FStar_List.hd nms in
                     match uu____8150 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___77_8156 ->
                          match uu___77_8156 with
                          | M uu____8157 -> true
                          | uu____8158 -> false) nms in
                   let uu____8159 =
                     let uu____8196 =
                       FStar_List.map2
                         (fun nm ->
                            fun uu____8286 ->
                              match uu____8286 with
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
                                       let uu____8463 =
                                         check env original_body (M t2) in
                                       (match uu____8463 with
                                        | (uu____8500, s_body1, u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8539, false) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____8196 in
                   (match uu____8159 with
                    | (nms1, s_branches, u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8723 ->
                                 match uu____8723 with
                                 | (pat, guard, s_body) ->
                                     let s_body1 =
                                       let uu____8774 =
                                         let uu____8775 =
                                           let uu____8790 =
                                             let uu____8797 =
                                               let uu____8802 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____8803 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____8802, uu____8803) in
                                             [uu____8797] in
                                           (s_body, uu____8790) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8775 in
                                       mk1 uu____8774 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____8835 =
                              let uu____8836 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8836] in
                            let uu____8837 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____8835 uu____8837
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.kprop)) in
                          let t1_star =
                            let uu____8843 =
                              let uu____8850 =
                                let uu____8851 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8851 in
                              [uu____8850] in
                            let uu____8852 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.kprop in
                            FStar_Syntax_Util.arrow uu____8843 uu____8852 in
                          let uu____8855 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____8894 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____8855, uu____8894)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____8911 =
                             let uu____8914 =
                               let uu____8915 =
                                 let uu____8942 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____8942,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8915 in
                             mk1 uu____8914 in
                           let uu____8979 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____8911, uu____8979))))
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
              let uu____9026 = FStar_Syntax_Syntax.mk_binder x in
              [uu____9026] in
            let uu____9027 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____9027 with
            | (x_binders1, e21) ->
                let uu____9040 = infer env e1 in
                (match uu____9040 with
                 | (N t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu____9057 = is_C t1 in
                       if uu____9057
                       then
                         let uu___95_9058 = binding in
                         let uu____9059 =
                           let uu____9062 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____9062 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___95_9058.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___95_9058.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9059;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___95_9058.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___95_9058.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___95_9058.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___95_9058.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding in
                     let env1 =
                       let uu___96_9065 = env in
                       let uu____9066 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___97_9068 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___97_9068.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___97_9068.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9066;
                         subst = (uu___96_9065.subst);
                         tc_const = (uu___96_9065.tc_const)
                       } in
                     let uu____9069 = proceed env1 e21 in
                     (match uu____9069 with
                      | (nm_rec, s_e2, u_e2) ->
                          let s_binding =
                            let uu___98_9086 = binding in
                            let uu____9087 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___98_9086.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___98_9086.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9087;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___98_9086.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___98_9086.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___98_9086.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___98_9086.FStar_Syntax_Syntax.lbpos)
                            } in
                          let uu____9090 =
                            let uu____9093 =
                              let uu____9094 =
                                let uu____9107 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___99_9117 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___99_9117.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___99_9117.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___99_9117.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___99_9117.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___99_9117.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___99_9117.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9107) in
                              FStar_Syntax_Syntax.Tm_let uu____9094 in
                            mk1 uu____9093 in
                          let uu____9118 =
                            let uu____9121 =
                              let uu____9122 =
                                let uu____9135 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___100_9145 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___100_9145.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___100_9145.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___100_9145.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___100_9145.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___100_9145.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___100_9145.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9135) in
                              FStar_Syntax_Syntax.Tm_let uu____9122 in
                            mk1 uu____9121 in
                          (nm_rec, uu____9090, uu____9118))
                 | (M t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu___101_9154 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___101_9154.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___101_9154.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___101_9154.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___101_9154.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___101_9154.FStar_Syntax_Syntax.lbpos)
                       } in
                     let env1 =
                       let uu___102_9156 = env in
                       let uu____9157 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___103_9159 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___103_9159.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___103_9159.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9157;
                         subst = (uu___102_9156.subst);
                         tc_const = (uu___102_9156.tc_const)
                       } in
                     let uu____9160 = ensure_m env1 e21 in
                     (match uu____9160 with
                      | (t2, s_e2, u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____9183 =
                              let uu____9184 =
                                let uu____9199 =
                                  let uu____9206 =
                                    let uu____9211 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____9212 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9211, uu____9212) in
                                  [uu____9206] in
                                (s_e2, uu____9199) in
                              FStar_Syntax_Syntax.Tm_app uu____9184 in
                            mk1 uu____9183 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.kprop)) in
                          let body =
                            let uu____9231 =
                              let uu____9232 =
                                let uu____9247 =
                                  let uu____9254 =
                                    let uu____9259 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____9259) in
                                  [uu____9254] in
                                (s_e1, uu____9247) in
                              FStar_Syntax_Syntax.Tm_app uu____9232 in
                            mk1 uu____9231 in
                          let uu____9274 =
                            let uu____9275 =
                              let uu____9276 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9276] in
                            FStar_Syntax_Util.abs uu____9275 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.kprop)) in
                          let uu____9277 =
                            let uu____9280 =
                              let uu____9281 =
                                let uu____9294 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___104_9304 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___104_9304.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___104_9304.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___104_9304.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___104_9304.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___104_9304.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___104_9304.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9294) in
                              FStar_Syntax_Syntax.Tm_let uu____9281 in
                            mk1 uu____9280 in
                          ((M t2), uu____9274, uu____9277)))
and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let mn =
        let uu____9316 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____9316 in
      let uu____9317 = check env e mn in
      match uu____9317 with
      | (N t, s_e, u_e) -> (t, s_e, u_e)
      | uu____9333 -> failwith "[check_n]: impossible"
and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun e ->
      let mn =
        let uu____9355 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____9355 in
      let uu____9356 = check env e mn in
      match uu____9356 with
      | (M t, s_e, u_e) -> (t, s_e, u_e)
      | uu____9372 -> failwith "[check_m]: impossible"
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
        (let uu____9402 =
           let uu____9403 = is_C c in Prims.op_Negation uu____9403 in
         if uu____9402 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____9411 =
           let uu____9412 = FStar_Syntax_Subst.compress c in
           uu____9412.FStar_Syntax_Syntax.n in
         match uu____9411 with
         | FStar_Syntax_Syntax.Tm_app (head1, args) ->
             let uu____9437 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9437 with
              | (wp_head, wp_args) ->
                  ((let uu____9475 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9489 =
                           let uu____9490 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9490 in
                         Prims.op_Negation uu____9489) in
                    if uu____9475 then failwith "mismatch" else ());
                   (let uu____9498 =
                      let uu____9499 =
                        let uu____9514 =
                          FStar_List.map2
                            (fun uu____9542 ->
                               fun uu____9543 ->
                                 match (uu____9542, uu____9543) with
                                 | ((arg, q), (wp_arg, q')) ->
                                     let print_implicit q1 =
                                       let uu____9580 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9580
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9583 =
                                           let uu____9588 =
                                             let uu____9589 =
                                               print_implicit q in
                                             let uu____9590 =
                                               print_implicit q' in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %b %b\n"
                                               uu____9589 uu____9590 in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9588) in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9583)
                                      else ();
                                      (let uu____9592 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9592, q)))) args wp_args in
                        (head1, uu____9514) in
                      FStar_Syntax_Syntax.Tm_app uu____9499 in
                    mk1 uu____9498)))
         | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9626 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9626 with
              | (binders_orig, comp1) ->
                  let uu____9633 =
                    let uu____9648 =
                      FStar_List.map
                        (fun uu____9682 ->
                           match uu____9682 with
                           | (bv, q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9702 = is_C h in
                               if uu____9702
                               then
                                 let w' =
                                   let uu____9714 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9714 in
                                 let uu____9715 =
                                   let uu____9722 =
                                     let uu____9729 =
                                       let uu____9734 =
                                         let uu____9735 =
                                           let uu____9736 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____9736 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9735 in
                                       (uu____9734, q) in
                                     [uu____9729] in
                                   (w', q) :: uu____9722 in
                                 (w', uu____9715)
                               else
                                 (let x =
                                    let uu____9757 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9757 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9648 in
                  (match uu____9633 with
                   | (bvs, binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____9812 =
                           let uu____9815 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9815 in
                         FStar_Syntax_Subst.subst_comp uu____9812 comp1 in
                       let app =
                         let uu____9819 =
                           let uu____9820 =
                             let uu____9835 =
                               FStar_List.map
                                 (fun bv ->
                                    let uu____9850 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____9851 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9850, uu____9851)) bvs in
                             (wp, uu____9835) in
                           FStar_Syntax_Syntax.Tm_app uu____9820 in
                         mk1 uu____9819 in
                       let comp3 =
                         let uu____9859 = type_of_comp comp2 in
                         let uu____9860 = is_monadic_comp comp2 in
                         trans_G env uu____9859 uu____9860 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e, uu____9862, uu____9863) ->
             trans_F_ env e wp
         | uu____9904 -> failwith "impossible trans_F_")
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
            let uu____9909 =
              let uu____9910 = star_type' env h in
              let uu____9913 =
                let uu____9922 =
                  let uu____9927 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____9927) in
                [uu____9922] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9910;
                FStar_Syntax_Syntax.effect_args = uu____9913;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____9909
          else
            (let uu____9937 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____9937)
let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.NoDeltaSteps;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env ->
    fun t -> let uu____9948 = n env.env t in star_type' env uu____9948
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple3)
  =
  fun env -> fun t -> let uu____9963 = n env.env t in check_n env uu____9963
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun c ->
      fun wp ->
        let uu____9973 = n env.env c in
        let uu____9974 = n env.env wp in trans_F_ env uu____9973 uu____9974