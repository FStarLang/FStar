open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ;}
let __proj__Mkenv__item__env: env -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
let __proj__Mkenv__item__subst:
  env -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
let __proj__Mkenv__item__tc_const:
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
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
              let uu___102_104 = a in
              let uu____105 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___102_104.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___102_104.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____105
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____115 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____115
             then
               (d "Elaborating extra WP combinators";
                (let uu____117 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____117))
             else ());
            (let rec collect_binders t =
               let uu____129 =
                 let uu____130 =
                   let uu____135 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____135 in
                 uu____130.FStar_Syntax_Syntax.n in
               match uu____129 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____174) -> t1
                     | uu____187 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____192 = collect_binders rest in
                   FStar_List.append bs uu____192
               | FStar_Syntax_Syntax.Tm_type uu____203 -> []
               | uu____208 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____226 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____226 FStar_Syntax_Util.name_binders in
             (let uu____246 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____246
              then
                let uu____247 =
                  let uu____248 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____248 in
                d uu____247
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____276 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____276 with
                | (sigelt,fv) ->
                    ((let uu____284 =
                        let uu____287 = FStar_ST.read sigelts in sigelt ::
                          uu____287 in
                      FStar_ST.write sigelts uu____284);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____325  ->
                     match uu____325 with
                     | (t,b) ->
                         let uu____336 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____336)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____367 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____367)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____390 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____390) in
              let uu____391 =
                let uu____410 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____438 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____438 in
                    let uu____443 =
                      let uu____444 =
                        let uu____451 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____452 =
                          let uu____455 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____455] in
                        uu____451 :: uu____452 in
                      FStar_List.append binders uu____444 in
                    FStar_Syntax_Util.abs uu____443 body
                      FStar_Pervasives_Native.None in
                  let uu____460 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____461 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____460, uu____461) in
                match uu____410 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____505 =
                        let uu____506 =
                          let uu____525 =
                            let uu____532 =
                              FStar_List.map
                                (fun uu____552  ->
                                   match uu____552 with
                                   | (bv,uu____562) ->
                                       let uu____563 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____564 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____563, uu____564)) binders in
                            let uu____565 =
                              let uu____572 =
                                let uu____577 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____578 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____577, uu____578) in
                              let uu____579 =
                                let uu____586 =
                                  let uu____591 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____591) in
                                [uu____586] in
                              uu____572 :: uu____579 in
                            FStar_List.append uu____532 uu____565 in
                          (fv, uu____525) in
                        FStar_Syntax_Syntax.Tm_app uu____506 in
                      mk1 uu____505 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____391 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____664 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____664 in
                    let ret1 =
                      let uu____668 =
                        let uu____669 =
                          let uu____674 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____674 in
                        FStar_Syntax_Util.residual_tot uu____669 in
                      FStar_Pervasives_Native.Some uu____668 in
                    let body =
                      let uu____676 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____676 ret1 in
                    let uu____677 =
                      let uu____678 = mk_all_implicit binders in
                      let uu____685 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____678 uu____685 in
                    FStar_Syntax_Util.abs uu____677 body ret1 in
                  let c_pure1 =
                    let uu____713 = mk_lid "pure" in
                    register env1 uu____713 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____718 =
                        let uu____719 =
                          let uu____720 =
                            let uu____727 =
                              let uu____728 =
                                let uu____729 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____729 in
                              FStar_Syntax_Syntax.mk_binder uu____728 in
                            [uu____727] in
                          let uu____730 =
                            let uu____735 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____735 in
                          FStar_Syntax_Util.arrow uu____720 uu____730 in
                        mk_gctx uu____719 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____718 in
                    let r =
                      let uu____737 =
                        let uu____738 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____738 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____737 in
                    let ret1 =
                      let uu____742 =
                        let uu____743 =
                          let uu____748 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____748 in
                        FStar_Syntax_Util.residual_tot uu____743 in
                      FStar_Pervasives_Native.Some uu____742 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____758 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____763 =
                          let uu____774 =
                            let uu____777 =
                              let uu____778 =
                                let uu____779 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____779
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____778 in
                            [uu____777] in
                          FStar_List.append gamma_as_args uu____774 in
                        FStar_Syntax_Util.mk_app uu____758 uu____763 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____784 =
                      let uu____785 = mk_all_implicit binders in
                      let uu____792 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____785 uu____792 in
                    FStar_Syntax_Util.abs uu____784 outer_body ret1 in
                  let c_app1 =
                    let uu____828 = mk_lid "app" in
                    register env1 uu____828 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____837 =
                        let uu____844 =
                          let uu____845 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____845 in
                        [uu____844] in
                      let uu____846 =
                        let uu____851 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____851 in
                      FStar_Syntax_Util.arrow uu____837 uu____846 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____854 =
                        let uu____855 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____855 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____854 in
                    let ret1 =
                      let uu____859 =
                        let uu____860 =
                          let uu____865 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____865 in
                        FStar_Syntax_Util.residual_tot uu____860 in
                      FStar_Pervasives_Native.Some uu____859 in
                    let uu____866 =
                      let uu____867 = mk_all_implicit binders in
                      let uu____874 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____867 uu____874 in
                    let uu____909 =
                      let uu____910 =
                        let uu____921 =
                          let uu____924 =
                            let uu____929 =
                              let uu____940 =
                                let uu____943 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____943] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____940 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____929 in
                          let uu____944 =
                            let uu____951 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____951] in
                          uu____924 :: uu____944 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____921 in
                      FStar_Syntax_Util.mk_app c_app1 uu____910 in
                    FStar_Syntax_Util.abs uu____866 uu____909 ret1 in
                  let c_lift11 =
                    let uu____957 = mk_lid "lift1" in
                    register env1 uu____957 c_lift1 in
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
                      let uu____967 =
                        let uu____974 =
                          let uu____975 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____975 in
                        let uu____976 =
                          let uu____979 =
                            let uu____980 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____980 in
                          [uu____979] in
                        uu____974 :: uu____976 in
                      let uu____981 =
                        let uu____986 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____986 in
                      FStar_Syntax_Util.arrow uu____967 uu____981 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____989 =
                        let uu____990 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____990 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____989 in
                    let a2 =
                      let uu____992 =
                        let uu____993 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____993 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____992 in
                    let ret1 =
                      let uu____997 =
                        let uu____998 =
                          let uu____1003 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____1003 in
                        FStar_Syntax_Util.residual_tot uu____998 in
                      FStar_Pervasives_Native.Some uu____997 in
                    let uu____1004 =
                      let uu____1005 = mk_all_implicit binders in
                      let uu____1012 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1005 uu____1012 in
                    let uu____1055 =
                      let uu____1056 =
                        let uu____1067 =
                          let uu____1070 =
                            let uu____1075 =
                              let uu____1086 =
                                let uu____1089 =
                                  let uu____1094 =
                                    let uu____1105 =
                                      let uu____1108 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1108] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1105 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1094 in
                                let uu____1109 =
                                  let uu____1116 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1116] in
                                uu____1089 :: uu____1109 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1086 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1075 in
                          let uu____1121 =
                            let uu____1128 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1128] in
                          uu____1070 :: uu____1121 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1067 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1056 in
                    FStar_Syntax_Util.abs uu____1004 uu____1055 ret1 in
                  let c_lift21 =
                    let uu____1134 = mk_lid "lift2" in
                    register env1 uu____1134 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1143 =
                        let uu____1150 =
                          let uu____1151 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1151 in
                        [uu____1150] in
                      let uu____1152 =
                        let uu____1157 =
                          let uu____1158 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1158 in
                        FStar_Syntax_Syntax.mk_Total uu____1157 in
                      FStar_Syntax_Util.arrow uu____1143 uu____1152 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1163 =
                        let uu____1164 =
                          let uu____1169 =
                            let uu____1170 =
                              let uu____1177 =
                                let uu____1178 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1178 in
                              [uu____1177] in
                            let uu____1179 =
                              let uu____1184 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1184 in
                            FStar_Syntax_Util.arrow uu____1170 uu____1179 in
                          mk_ctx uu____1169 in
                        FStar_Syntax_Util.residual_tot uu____1164 in
                      FStar_Pervasives_Native.Some uu____1163 in
                    let e1 =
                      let uu____1186 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1186 in
                    let body =
                      let uu____1188 =
                        let uu____1189 =
                          let uu____1196 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1196] in
                        FStar_List.append gamma uu____1189 in
                      let uu____1201 =
                        let uu____1202 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1207 =
                          let uu____1218 =
                            let uu____1219 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1219 in
                          let uu____1220 = args_of_binders1 gamma in
                          uu____1218 :: uu____1220 in
                        FStar_Syntax_Util.mk_app uu____1202 uu____1207 in
                      FStar_Syntax_Util.abs uu____1188 uu____1201 ret1 in
                    let uu____1223 =
                      let uu____1224 = mk_all_implicit binders in
                      let uu____1231 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1224 uu____1231 in
                    FStar_Syntax_Util.abs uu____1223 body ret1 in
                  let c_push1 =
                    let uu____1263 = mk_lid "push" in
                    register env1 uu____1263 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1291 =
                        let uu____1292 =
                          let uu____1311 = args_of_binders1 binders in
                          (c, uu____1311) in
                        FStar_Syntax_Syntax.Tm_app uu____1292 in
                      mk1 uu____1291
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1323 =
                        let uu____1324 =
                          let uu____1331 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1332 =
                            let uu____1335 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1335] in
                          uu____1331 :: uu____1332 in
                        let uu____1336 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1324 uu____1336 in
                      FStar_Syntax_Syntax.mk_Total uu____1323 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1342 =
                      let uu____1343 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1343 in
                    let uu____1354 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1356 =
                        let uu____1361 =
                          let uu____1372 =
                            let uu____1375 =
                              let uu____1380 =
                                let uu____1391 =
                                  let uu____1392 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1392 in
                                [uu____1391] in
                              FStar_Syntax_Util.mk_app l_ite uu____1380 in
                            [uu____1375] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1372 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1361 in
                      FStar_Syntax_Util.ascribe uu____1356
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1342 uu____1354
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1424 = mk_lid "wp_if_then_else" in
                    register env1 uu____1424 wp_if_then_else in
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
                      let uu____1439 =
                        let uu____1450 =
                          let uu____1453 =
                            let uu____1458 =
                              let uu____1469 =
                                let uu____1472 =
                                  let uu____1477 =
                                    let uu____1488 =
                                      let uu____1489 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1489 in
                                    [uu____1488] in
                                  FStar_Syntax_Util.mk_app l_and uu____1477 in
                                [uu____1472] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1469 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1458 in
                          let uu____1498 =
                            let uu____1505 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1505] in
                          uu____1453 :: uu____1498 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1450 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1439 in
                    let uu____1510 =
                      let uu____1511 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1511 in
                    FStar_Syntax_Util.abs uu____1510 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1523 = mk_lid "wp_assert" in
                    register env1 uu____1523 wp_assert in
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
                      let uu____1538 =
                        let uu____1549 =
                          let uu____1552 =
                            let uu____1557 =
                              let uu____1568 =
                                let uu____1571 =
                                  let uu____1576 =
                                    let uu____1587 =
                                      let uu____1588 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1588 in
                                    [uu____1587] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1576 in
                                [uu____1571] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1568 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1557 in
                          let uu____1597 =
                            let uu____1604 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1604] in
                          uu____1552 :: uu____1597 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1549 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1538 in
                    let uu____1609 =
                      let uu____1610 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1610 in
                    FStar_Syntax_Util.abs uu____1609 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1622 = mk_lid "wp_assume" in
                    register env1 uu____1622 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1635 =
                        let uu____1642 =
                          let uu____1643 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1643 in
                        [uu____1642] in
                      let uu____1644 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1635 uu____1644 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1655 =
                        let uu____1666 =
                          let uu____1669 =
                            let uu____1674 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1674 in
                          let uu____1685 =
                            let uu____1692 =
                              let uu____1697 =
                                let uu____1708 =
                                  let uu____1711 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1711] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1708 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1697 in
                            [uu____1692] in
                          uu____1669 :: uu____1685 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1666 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1655 in
                    let uu____1724 =
                      let uu____1725 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1725 in
                    FStar_Syntax_Util.abs uu____1724 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1737 = mk_lid "wp_close" in
                    register env1 uu____1737 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1749 =
                      let uu____1750 =
                        let uu____1751 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1751 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1750 in
                    FStar_Pervasives_Native.Some uu____1749 in
                  let mk_forall1 x body =
                    let uu____1767 =
                      let uu____1772 =
                        let uu____1773 =
                          let uu____1792 =
                            let uu____1795 =
                              let uu____1796 =
                                let uu____1797 =
                                  let uu____1798 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1798] in
                                FStar_Syntax_Util.abs uu____1797 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1796 in
                            [uu____1795] in
                          (FStar_Syntax_Util.tforall, uu____1792) in
                        FStar_Syntax_Syntax.Tm_app uu____1773 in
                      FStar_Syntax_Syntax.mk uu____1772 in
                    uu____1767 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1809 =
                      let uu____1810 = FStar_Syntax_Subst.compress t in
                      uu____1810.FStar_Syntax_Syntax.n in
                    match uu____1809 with
                    | FStar_Syntax_Syntax.Tm_type uu____1815 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1845  ->
                              match uu____1845 with
                              | (b,uu____1851) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1852 -> true in
                  let rec is_monotonic t =
                    let uu____1857 =
                      let uu____1858 = FStar_Syntax_Subst.compress t in
                      uu____1858.FStar_Syntax_Syntax.n in
                    match uu____1857 with
                    | FStar_Syntax_Syntax.Tm_type uu____1863 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1893  ->
                              match uu____1893 with
                              | (b,uu____1899) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1900 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1972 =
                      let uu____1973 = FStar_Syntax_Subst.compress t1 in
                      uu____1973.FStar_Syntax_Syntax.n in
                    match uu____1972 with
                    | FStar_Syntax_Syntax.Tm_type uu____1978 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1981);
                                      FStar_Syntax_Syntax.tk = uu____1982;
                                      FStar_Syntax_Syntax.pos = uu____1983;
                                      FStar_Syntax_Syntax.vars = uu____1984;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2028 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2028
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2031 =
                              let uu____2036 =
                                let uu____2047 =
                                  let uu____2048 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2048 in
                                [uu____2047] in
                              FStar_Syntax_Util.mk_app x uu____2036 in
                            let uu____2049 =
                              let uu____2054 =
                                let uu____2065 =
                                  let uu____2066 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2066 in
                                [uu____2065] in
                              FStar_Syntax_Util.mk_app y uu____2054 in
                            mk_rel1 b uu____2031 uu____2049 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2071 =
                               let uu____2072 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2077 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2072 uu____2077 in
                             let uu____2082 =
                               let uu____2083 =
                                 let uu____2088 =
                                   let uu____2099 =
                                     let uu____2100 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2100 in
                                   [uu____2099] in
                                 FStar_Syntax_Util.mk_app x uu____2088 in
                               let uu____2101 =
                                 let uu____2106 =
                                   let uu____2117 =
                                     let uu____2118 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2118 in
                                   [uu____2117] in
                                 FStar_Syntax_Util.mk_app y uu____2106 in
                               mk_rel1 b uu____2083 uu____2101 in
                             FStar_Syntax_Util.mk_imp uu____2071 uu____2082 in
                           let uu____2119 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2119)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2122);
                                      FStar_Syntax_Syntax.tk = uu____2123;
                                      FStar_Syntax_Syntax.pos = uu____2124;
                                      FStar_Syntax_Syntax.vars = uu____2125;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____2169 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____2169
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____2172 =
                              let uu____2177 =
                                let uu____2188 =
                                  let uu____2189 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2189 in
                                [uu____2188] in
                              FStar_Syntax_Util.mk_app x uu____2177 in
                            let uu____2190 =
                              let uu____2195 =
                                let uu____2206 =
                                  let uu____2207 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____2207 in
                                [uu____2206] in
                              FStar_Syntax_Util.mk_app y uu____2195 in
                            mk_rel1 b uu____2172 uu____2190 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2212 =
                               let uu____2213 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2218 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2213 uu____2218 in
                             let uu____2223 =
                               let uu____2224 =
                                 let uu____2229 =
                                   let uu____2240 =
                                     let uu____2241 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2241 in
                                   [uu____2240] in
                                 FStar_Syntax_Util.mk_app x uu____2229 in
                               let uu____2242 =
                                 let uu____2247 =
                                   let uu____2258 =
                                     let uu____2259 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2259 in
                                   [uu____2258] in
                                 FStar_Syntax_Util.mk_app y uu____2247 in
                               mk_rel1 b uu____2224 uu____2242 in
                             FStar_Syntax_Util.mk_imp uu____2212 uu____2223 in
                           let uu____2260 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2260)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___103_2297 = t1 in
                          let uu____2298 =
                            let uu____2299 =
                              let uu____2314 =
                                let uu____2315 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2315 in
                              ([binder], uu____2314) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2299 in
                          {
                            FStar_Syntax_Syntax.n = uu____2298;
                            FStar_Syntax_Syntax.tk =
                              (uu___103_2297.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___103_2297.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___103_2297.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2330 ->
                        failwith "unhandled arrow"
                    | uu____2345 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2360 =
                        let uu____2361 = FStar_Syntax_Subst.compress t1 in
                        uu____2361.FStar_Syntax_Syntax.n in
                      match uu____2360 with
                      | FStar_Syntax_Syntax.Tm_type uu____2366 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2397 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2397
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2418 =
                                let uu____2419 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2419 i in
                              FStar_Syntax_Syntax.fvar uu____2418
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2454 =
                            let uu____2461 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2475  ->
                                     match uu____2475 with
                                     | (t2,q) ->
                                         let uu____2482 = project i x in
                                         let uu____2483 = project i y in
                                         mk_stronger t2 uu____2482 uu____2483)
                                args in
                            match uu____2461 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2454 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2510);
                                      FStar_Syntax_Syntax.tk = uu____2511;
                                      FStar_Syntax_Syntax.pos = uu____2512;
                                      FStar_Syntax_Syntax.vars = uu____2513;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2559  ->
                                   match uu____2559 with
                                   | (bv,q) ->
                                       let uu____2566 =
                                         let uu____2567 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2567 in
                                       FStar_Syntax_Syntax.gen_bv uu____2566
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2574 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2574) bvs in
                          let body =
                            let uu____2576 = FStar_Syntax_Util.mk_app x args in
                            let uu____2577 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2576 uu____2577 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2584);
                                      FStar_Syntax_Syntax.tk = uu____2585;
                                      FStar_Syntax_Syntax.pos = uu____2586;
                                      FStar_Syntax_Syntax.vars = uu____2587;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2633  ->
                                   match uu____2633 with
                                   | (bv,q) ->
                                       let uu____2640 =
                                         let uu____2641 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2641 in
                                       FStar_Syntax_Syntax.gen_bv uu____2640
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2648 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2648) bvs in
                          let body =
                            let uu____2650 = FStar_Syntax_Util.mk_app x args in
                            let uu____2651 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2650 uu____2651 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2656 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2658 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2659 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2660 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2658 uu____2659 uu____2660 in
                    let uu____2661 =
                      let uu____2662 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2662 in
                    FStar_Syntax_Util.abs uu____2661 body ret_tot_type in
                  let stronger1 =
                    let uu____2690 = mk_lid "stronger" in
                    register env1 uu____2690 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2698 = FStar_Util.prefix gamma in
                    match uu____2698 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2743 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2743 in
                          let uu____2748 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2748 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2760 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2760 in
                              let guard_free1 =
                                let uu____2772 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2772 in
                              let pat =
                                let uu____2778 =
                                  let uu____2789 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2789] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2778 in
                              let pattern_guarded_body =
                                let uu____2795 =
                                  let uu____2796 =
                                    let uu____2805 =
                                      let uu____2806 =
                                        let uu____2819 =
                                          let uu____2822 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2822] in
                                        [uu____2819] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2806 in
                                    (body, uu____2805) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2796 in
                                mk1 uu____2795 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2827 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2831 =
                            let uu____2832 =
                              let uu____2833 =
                                let uu____2834 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2839 =
                                  let uu____2850 = args_of_binders1 wp_args in
                                  let uu____2853 =
                                    let uu____2856 =
                                      let uu____2857 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2857 in
                                    [uu____2856] in
                                  FStar_List.append uu____2850 uu____2853 in
                                FStar_Syntax_Util.mk_app uu____2834
                                  uu____2839 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2833 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2832 in
                          FStar_Syntax_Util.abs gamma uu____2831
                            ret_gtot_type in
                        let uu____2858 =
                          let uu____2859 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2859 in
                        FStar_Syntax_Util.abs uu____2858 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2871 = mk_lid "wp_ite" in
                    register env1 uu____2871 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2879 = FStar_Util.prefix gamma in
                    match uu____2879 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2922 =
                            let uu____2923 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2928 =
                              let uu____2939 =
                                let uu____2940 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2940 in
                              [uu____2939] in
                            FStar_Syntax_Util.mk_app uu____2923 uu____2928 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2922 in
                        let uu____2941 =
                          let uu____2942 =
                            let uu____2949 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2949 gamma in
                          FStar_List.append binders uu____2942 in
                        FStar_Syntax_Util.abs uu____2941 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2965 = mk_lid "null_wp" in
                    register env1 uu____2965 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2978 =
                        let uu____2989 =
                          let uu____2992 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2993 =
                            let uu____2996 =
                              let uu____3001 =
                                let uu____3012 =
                                  let uu____3013 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____3013 in
                                [uu____3012] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____3001 in
                            let uu____3014 =
                              let uu____3021 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____3021] in
                            uu____2996 :: uu____3014 in
                          uu____2992 :: uu____2993 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2989 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2978 in
                    let uu____3026 =
                      let uu____3027 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____3027 in
                    FStar_Syntax_Util.abs uu____3026 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____3039 = mk_lid "wp_trivial" in
                    register env1 uu____3039 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____3046 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____3046
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____3051 =
                      let uu____3054 = FStar_ST.read sigelts in
                      FStar_List.rev uu____3054 in
                    let uu____3061 =
                      let uu___104_3062 = ed in
                      let uu____3063 =
                        let uu____3064 = c wp_if_then_else2 in
                        ([], uu____3064) in
                      let uu____3067 =
                        let uu____3068 = c wp_ite2 in ([], uu____3068) in
                      let uu____3071 =
                        let uu____3072 = c stronger2 in ([], uu____3072) in
                      let uu____3075 =
                        let uu____3076 = c wp_close2 in ([], uu____3076) in
                      let uu____3079 =
                        let uu____3080 = c wp_assert2 in ([], uu____3080) in
                      let uu____3083 =
                        let uu____3084 = c wp_assume2 in ([], uu____3084) in
                      let uu____3087 =
                        let uu____3088 = c null_wp2 in ([], uu____3088) in
                      let uu____3091 =
                        let uu____3092 = c wp_trivial2 in ([], uu____3092) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___104_3062.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___104_3062.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___104_3062.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___104_3062.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___104_3062.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___104_3062.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___104_3062.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____3063;
                        FStar_Syntax_Syntax.ite_wp = uu____3067;
                        FStar_Syntax_Syntax.stronger = uu____3071;
                        FStar_Syntax_Syntax.close_wp = uu____3075;
                        FStar_Syntax_Syntax.assert_p = uu____3079;
                        FStar_Syntax_Syntax.assume_p = uu____3083;
                        FStar_Syntax_Syntax.null_wp = uu____3087;
                        FStar_Syntax_Syntax.trivial = uu____3091;
                        FStar_Syntax_Syntax.repr =
                          (uu___104_3062.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___104_3062.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___104_3062.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___104_3062.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____3051, uu____3061)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___105_3109 = dmff_env in
      {
        env = env';
        subst = (uu___105_3109.subst);
        tc_const = (uu___105_3109.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____3123 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____3137 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___91_3149  ->
    match uu___91_3149 with
    | FStar_Syntax_Syntax.Total (t,uu____3151) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___90_3168  ->
                match uu___90_3168 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3169 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____3171 =
          let uu____3172 =
            let uu____3173 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____3173 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____3172 in
        failwith uu____3171
    | FStar_Syntax_Syntax.GTotal uu____3174 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___92_3188  ->
    match uu___92_3188 with
    | N t ->
        let uu____3190 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____3190
    | M t ->
        let uu____3192 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____3192
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3197,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____3199;
                      FStar_Syntax_Syntax.pos = uu____3200;
                      FStar_Syntax_Syntax.vars = uu____3201;_})
        -> nm_of_comp n2
    | uu____3222 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____3240 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____3240 with | M uu____3241 -> true | N uu____3242 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3247 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____3260 =
        let uu____3267 =
          let uu____3268 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3268 in
        [uu____3267] in
      let uu____3269 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____3260 uu____3269 in
    let uu____3274 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____3274
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
          (let uu____3327 =
             let uu____3342 =
               let uu____3349 =
                 let uu____3354 =
                   let uu____3355 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____3355 in
                 let uu____3356 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____3354, uu____3356) in
               [uu____3349] in
             let uu____3365 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____3342, uu____3365) in
           FStar_Syntax_Syntax.Tm_arrow uu____3327)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3401) ->
          let binders1 =
            FStar_List.map
              (fun uu____3441  ->
                 match uu____3441 with
                 | (bv,aqual) ->
                     let uu____3452 =
                       let uu___106_3453 = bv in
                       let uu____3454 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_3453.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_3453.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3454
                       } in
                     (uu____3452, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3459,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3461);
                             FStar_Syntax_Syntax.tk = uu____3462;
                             FStar_Syntax_Syntax.pos = uu____3463;
                             FStar_Syntax_Syntax.vars = uu____3464;_})
               ->
               let uu____3497 =
                 let uu____3498 =
                   let uu____3513 =
                     let uu____3514 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3514 in
                   (binders1, uu____3513) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3498 in
               mk1 uu____3497
           | uu____3521 ->
               let uu____3522 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3522 with
                | N hn ->
                    let uu____3524 =
                      let uu____3525 =
                        let uu____3540 =
                          let uu____3541 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3541 in
                        (binders1, uu____3540) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3525 in
                    mk1 uu____3524
                | M a ->
                    let uu____3549 =
                      let uu____3550 =
                        let uu____3565 =
                          let uu____3572 =
                            let uu____3579 =
                              let uu____3584 =
                                let uu____3585 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3585 in
                              let uu____3586 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3584, uu____3586) in
                            [uu____3579] in
                          FStar_List.append binders1 uu____3572 in
                        let uu____3599 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3565, uu____3599) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3550 in
                    mk1 uu____3549))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3673 = f x in
                    FStar_Util.string_builder_append strb uu____3673);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3680 = f x1 in
                         FStar_Util.string_builder_append strb uu____3680))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3682 = FStar_Syntax_Print.term_to_string t2 in
            let uu____3683 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____3682 uu____3683 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3691 =
              let uu____3692 = FStar_Syntax_Subst.compress ty in
              uu____3692.FStar_Syntax_Syntax.n in
            match uu____3691 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3719 =
                  let uu____3720 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3720 in
                if uu____3719
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3746 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3746 s in
                       let uu____3749 =
                         let uu____3750 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3750 in
                       if uu____3749
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____3753 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3753 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3775  ->
                                  match uu____3775 with
                                  | (bv,uu____3785) ->
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
            | uu____3801 ->
                ((let uu____3803 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____3803);
                 false) in
          let rec is_valid_application head2 =
            let uu____3808 =
              let uu____3809 = FStar_Syntax_Subst.compress head2 in
              uu____3809.FStar_Syntax_Syntax.n in
            match uu____3808 with
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
                  (let uu____3816 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3816)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3818 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3818 with
                 | ((uu____3827,ty),uu____3829) ->
                     let uu____3834 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3834
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3844 -> true
                        | uu____3863 ->
                            ((let uu____3865 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____3865);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3867 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3868 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3870) ->
                is_valid_application t2
            | uu____3879 -> false in
          let uu____3880 = is_valid_application head1 in
          if uu____3880
          then
            let uu____3881 =
              let uu____3882 =
                let uu____3901 =
                  FStar_List.map
                    (fun uu____3924  ->
                       match uu____3924 with
                       | (t2,qual) ->
                           let uu____3947 = star_type' env t2 in
                           (uu____3947, qual)) args in
                (head1, uu____3901) in
              FStar_Syntax_Syntax.Tm_app uu____3882 in
            mk1 uu____3881
          else
            (let uu____3959 =
               let uu____3960 =
                 let uu____3961 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3961 in
               FStar_Errors.Err uu____3960 in
             raise uu____3959)
      | FStar_Syntax_Syntax.Tm_bvar uu____3962 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3963 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3964 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3965 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3993 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3993 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___109_4001 = env in
                 let uu____4002 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____4002;
                   subst = (uu___109_4001.subst);
                   tc_const = (uu___109_4001.tc_const)
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
               ((let uu___110_4026 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___110_4026.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___110_4026.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____4037 =
            let uu____4038 =
              let uu____4047 = star_type' env t2 in (uu____4047, m) in
            FStar_Syntax_Syntax.Tm_meta uu____4038 in
          mk1 uu____4037
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____4119 =
            let uu____4120 =
              let uu____4155 = star_type' env e in
              let uu____4156 =
                let uu____4175 =
                  let uu____4184 = star_type' env t2 in
                  FStar_Util.Inl uu____4184 in
                (uu____4175, FStar_Pervasives_Native.None) in
              (uu____4155, uu____4156, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____4120 in
          mk1 uu____4119
      | FStar_Syntax_Syntax.Tm_ascribed uu____4227 ->
          let uu____4262 =
            let uu____4263 =
              let uu____4264 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____4264 in
            FStar_Errors.Err uu____4263 in
          raise uu____4262
      | FStar_Syntax_Syntax.Tm_refine uu____4265 ->
          let uu____4274 =
            let uu____4275 =
              let uu____4276 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4276 in
            FStar_Errors.Err uu____4275 in
          raise uu____4274
      | FStar_Syntax_Syntax.Tm_uinst uu____4277 ->
          let uu____4286 =
            let uu____4287 =
              let uu____4288 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4288 in
            FStar_Errors.Err uu____4287 in
          raise uu____4286
      | FStar_Syntax_Syntax.Tm_constant uu____4289 ->
          let uu____4290 =
            let uu____4291 =
              let uu____4292 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4292 in
            FStar_Errors.Err uu____4291 in
          raise uu____4290
      | FStar_Syntax_Syntax.Tm_match uu____4293 ->
          let uu____4322 =
            let uu____4323 =
              let uu____4324 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4324 in
            FStar_Errors.Err uu____4323 in
          raise uu____4322
      | FStar_Syntax_Syntax.Tm_let uu____4325 ->
          let uu____4340 =
            let uu____4341 =
              let uu____4342 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4342 in
            FStar_Errors.Err uu____4341 in
          raise uu____4340
      | FStar_Syntax_Syntax.Tm_uvar uu____4343 ->
          let uu____4364 =
            let uu____4365 =
              let uu____4366 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4366 in
            FStar_Errors.Err uu____4365 in
          raise uu____4364
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4367 =
            let uu____4368 =
              let uu____4369 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4369 in
            FStar_Errors.Err uu____4368 in
          raise uu____4367
      | FStar_Syntax_Syntax.Tm_delayed uu____4370 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___94_4404  ->
    match uu___94_4404 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___93_4411  ->
                match uu___93_4411 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4412 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____4417 =
      let uu____4418 = FStar_Syntax_Subst.compress t in
      uu____4418.FStar_Syntax_Syntax.n in
    match uu____4417 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4454 =
            let uu____4455 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____4455 in
          is_C uu____4454 in
        if r
        then
          ((let uu____4477 =
              let uu____4478 =
                FStar_List.for_all
                  (fun uu____4486  ->
                     match uu____4486 with | (h,uu____4492) -> is_C h) args in
              Prims.op_Negation uu____4478 in
            if uu____4477 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4496 =
              let uu____4497 =
                FStar_List.for_all
                  (fun uu____4506  ->
                     match uu____4506 with
                     | (h,uu____4512) ->
                         let uu____4513 = is_C h in
                         Prims.op_Negation uu____4513) args in
              Prims.op_Negation uu____4497 in
            if uu____4496 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4537 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4537 with
         | M t1 ->
             ((let uu____4540 = is_C t1 in
               if uu____4540 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4544) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4554) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4564,uu____4565) -> is_C t1
    | uu____4622 -> false
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
          let uu____4654 =
            let uu____4655 =
              let uu____4674 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4675 =
                let uu____4682 =
                  let uu____4687 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4687) in
                [uu____4682] in
              (uu____4674, uu____4675) in
            FStar_Syntax_Syntax.Tm_app uu____4655 in
          mk1 uu____4654 in
        let uu____4702 =
          let uu____4703 = FStar_Syntax_Syntax.mk_binder p in [uu____4703] in
        FStar_Syntax_Util.abs uu____4702 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___95_4707  ->
    match uu___95_4707 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4708 -> false
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
        let return_if uu____4893 =
          match uu____4893 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4924 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4926 =
                       let uu____4927 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4927 in
                     Prims.op_Negation uu____4926) in
                if uu____4924
                then
                  let uu____4928 =
                    let uu____4929 =
                      let uu____4930 = FStar_Syntax_Print.term_to_string e in
                      let uu____4931 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4932 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4930 uu____4931 uu____4932 in
                    FStar_Errors.Err uu____4929 in
                  raise uu____4928
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4949 = mk_return env t1 s_e in
                     ((M t1), uu____4949, u_e)))
               | (M t1,N t2) ->
                   let uu____4952 =
                     let uu____4953 =
                       let uu____4954 = FStar_Syntax_Print.term_to_string e in
                       let uu____4955 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4956 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4954 uu____4955 uu____4956 in
                     FStar_Errors.Err uu____4953 in
                   raise uu____4952) in
        let ensure_m env1 e2 =
          let strip_m uu___96_4997 =
            match uu___96_4997 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____5013 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____5033 =
                let uu____5034 =
                  let uu____5039 =
                    let uu____5040 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____5040 in
                  (uu____5039, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____5034 in
              raise uu____5033
          | M uu____5047 ->
              let uu____5048 = check env1 e2 context_nm in strip_m uu____5048 in
        let uu____5055 =
          let uu____5056 = FStar_Syntax_Subst.compress e in
          uu____5056.FStar_Syntax_Syntax.n in
        match uu____5055 with
        | FStar_Syntax_Syntax.Tm_bvar uu____5067 ->
            let uu____5068 = infer env e in return_if uu____5068
        | FStar_Syntax_Syntax.Tm_name uu____5075 ->
            let uu____5076 = infer env e in return_if uu____5076
        | FStar_Syntax_Syntax.Tm_fvar uu____5083 ->
            let uu____5084 = infer env e in return_if uu____5084
        | FStar_Syntax_Syntax.Tm_abs uu____5091 ->
            let uu____5110 = infer env e in return_if uu____5110
        | FStar_Syntax_Syntax.Tm_constant uu____5117 ->
            let uu____5118 = infer env e in return_if uu____5118
        | FStar_Syntax_Syntax.Tm_app uu____5125 ->
            let uu____5144 = infer env e in return_if uu____5144
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5228) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5238) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5248,uu____5249) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5306 ->
            let uu____5321 =
              let uu____5322 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5322 in
            failwith uu____5321
        | FStar_Syntax_Syntax.Tm_type uu____5329 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5336 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5357 ->
            let uu____5366 =
              let uu____5367 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5367 in
            failwith uu____5366
        | FStar_Syntax_Syntax.Tm_uvar uu____5374 ->
            let uu____5395 =
              let uu____5396 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5396 in
            failwith uu____5395
        | FStar_Syntax_Syntax.Tm_delayed uu____5403 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5438 =
              let uu____5439 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5439 in
            failwith uu____5438
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
      let uu____5465 =
        let uu____5466 = FStar_Syntax_Subst.compress e in
        uu____5466.FStar_Syntax_Syntax.n in
      match uu____5465 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5531;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5532;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5540 =
                  let uu___111_5541 = rc in
                  let uu____5542 =
                    let uu____5549 =
                      let uu____5550 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____5550 in
                    FStar_Pervasives_Native.Some uu____5549 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___111_5541.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5542;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___111_5541.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____5540 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___112_5562 = env in
            let uu____5563 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____5563;
              subst = (uu___112_5562.subst);
              tc_const = (uu___112_5562.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____5583  ->
                 match uu____5583 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_5596 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_5596.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_5596.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____5597 =
            FStar_List.fold_left
              (fun uu____5626  ->
                 fun uu____5627  ->
                   match (uu____5626, uu____5627) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5677 = is_C c in
                       if uu____5677
                       then
                         let xw =
                           let uu____5685 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5685 in
                         let x =
                           let uu___114_5687 = bv in
                           let uu____5688 =
                             let uu____5693 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5693 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_5687.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_5687.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5688
                           } in
                         let env3 =
                           let uu___115_5695 = env2 in
                           let uu____5696 =
                             let uu____5699 =
                               let uu____5700 =
                                 let uu____5709 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5709) in
                               FStar_Syntax_Syntax.NT uu____5700 in
                             uu____5699 :: (env2.subst) in
                           {
                             env = (uu___115_5695.env);
                             subst = uu____5696;
                             tc_const = (uu___115_5695.tc_const)
                           } in
                         let uu____5710 =
                           let uu____5713 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5714 =
                             let uu____5717 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5717 :: acc in
                           uu____5713 :: uu____5714 in
                         (env3, uu____5710)
                       else
                         (let x =
                            let uu___116_5722 = bv in
                            let uu____5723 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_5722.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_5722.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5723
                            } in
                          let uu____5728 =
                            let uu____5731 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5731 :: acc in
                          (env2, uu____5728))) (env1, []) binders1 in
          (match uu____5597 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5751 =
                 let check_what =
                   let uu____5769 = is_monadic rc_opt1 in
                   if uu____5769 then check_m else check_n in
                 let uu____5781 = check_what env2 body1 in
                 match uu____5781 with
                 | (t,s_body,u_body) ->
                     let uu____5797 =
                       let uu____5798 =
                         let uu____5799 = is_monadic rc_opt1 in
                         if uu____5799 then M t else N t in
                       comp_of_nm uu____5798 in
                     (uu____5797, s_body, u_body) in
               (match uu____5751 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____5828 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___97_5832  ->
                                           match uu___97_5832 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5833 -> false)) in
                                 if uu____5828
                                 then
                                   let uu____5834 =
                                     FStar_List.filter
                                       (fun uu___98_5838  ->
                                          match uu___98_5838 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5839 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5834
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5854 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___99_5858  ->
                                         match uu___99_5858 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5859 -> false)) in
                               if uu____5854
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___100_5866  ->
                                        match uu___100_5866 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5867 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5868 =
                                   let uu____5869 =
                                     let uu____5876 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5876 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5869 flags in
                                 FStar_Pervasives_Native.Some uu____5868
                               else
                                 (let uu____5878 =
                                    let uu___117_5879 = rc in
                                    let uu____5880 =
                                      let uu____5887 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5887 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_5879.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5880;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_5879.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5878)) in
                    let uu____5888 =
                      let comp1 =
                        let uu____5900 = is_monadic rc_opt1 in
                        let uu____5901 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5900 uu____5901 in
                      let uu____5902 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5902,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5888 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5962 =
                             let uu____5963 =
                               let uu____5982 =
                                 let uu____5985 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5985 s_rc_opt in
                               (s_binders1, s_body1, uu____5982) in
                             FStar_Syntax_Syntax.Tm_abs uu____5963 in
                           mk1 uu____5962 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5997 =
                             let uu____5998 =
                               let uu____6017 =
                                 let uu____6020 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____6020 u_rc_opt in
                               (u_binders2, u_body2, uu____6017) in
                             FStar_Syntax_Syntax.Tm_abs uu____5998 in
                           mk1 uu____5997 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____6034;_};
            FStar_Syntax_Syntax.fv_delta = uu____6035;
            FStar_Syntax_Syntax.fv_qual = uu____6036;_}
          ->
          let uu____6039 =
            let uu____6044 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6044 in
          (match uu____6039 with
           | (uu____6075,t) ->
               let uu____6077 = let uu____6078 = normalize1 t in N uu____6078 in
               (uu____6077, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6109 = check_n env head1 in
          (match uu____6109 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6129 =
                   let uu____6130 = FStar_Syntax_Subst.compress t in
                   uu____6130.FStar_Syntax_Syntax.n in
                 match uu____6129 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6135 -> true
                 | uu____6150 -> false in
               let rec flatten1 t =
                 let uu____6169 =
                   let uu____6170 = FStar_Syntax_Subst.compress t in
                   uu____6170.FStar_Syntax_Syntax.n in
                 match uu____6169 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6191);
                                FStar_Syntax_Syntax.tk = uu____6192;
                                FStar_Syntax_Syntax.pos = uu____6193;
                                FStar_Syntax_Syntax.vars = uu____6194;_})
                     when is_arrow t1 ->
                     let uu____6227 = flatten1 t1 in
                     (match uu____6227 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6325,uu____6326)
                     -> flatten1 e1
                 | uu____6383 ->
                     let uu____6384 =
                       let uu____6385 =
                         let uu____6386 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6386 in
                       FStar_Errors.Err uu____6385 in
                     raise uu____6384 in
               let uu____6401 = flatten1 t_head in
               (match uu____6401 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6471 =
                          let uu____6472 =
                            let uu____6473 = FStar_Util.string_of_int n1 in
                            let uu____6480 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____6491 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6473 uu____6480 uu____6491 in
                          FStar_Errors.Err uu____6472 in
                        raise uu____6471)
                     else ();
                     (let uu____6499 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____6499 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6542 args1 =
                            match uu____6542 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6624 =
                                       let uu____6625 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____6625.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____6624
                                 | (binders3,[]) ->
                                     let uu____6661 =
                                       let uu____6662 =
                                         let uu____6667 =
                                           let uu____6668 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6668 in
                                         FStar_Syntax_Subst.compress
                                           uu____6667 in
                                       uu____6662.FStar_Syntax_Syntax.n in
                                     (match uu____6661 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6697 =
                                            let uu____6698 =
                                              let uu____6699 =
                                                let uu____6714 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____6714) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6699 in
                                            mk1 uu____6698 in
                                          N uu____6697
                                      | uu____6721 -> failwith "wat?")
                                 | ([],uu____6722::uu____6723) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6771)::binders3,(arg,uu____6774)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____6839 = FStar_List.splitAt n' binders1 in
                          (match uu____6839 with
                           | (binders2,uu____6871) ->
                               let uu____6896 =
                                 let uu____6915 =
                                   FStar_List.map2
                                     (fun uu____6963  ->
                                        fun uu____6964  ->
                                          match (uu____6963, uu____6964) with
                                          | ((bv,uu____6996),(arg,q)) ->
                                              let uu____7007 =
                                                let uu____7008 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____7008.FStar_Syntax_Syntax.n in
                                              (match uu____7007 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7027 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____7051 ->
                                                   let uu____7052 =
                                                     check_n env arg in
                                                   (match uu____7052 with
                                                    | (uu____7073,s_arg,u_arg)
                                                        ->
                                                        let uu____7076 =
                                                          let uu____7083 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7083
                                                          then
                                                            let uu____7090 =
                                                              let uu____7095
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7095, q) in
                                                            [uu____7090;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7076))))
                                     binders2 args in
                                 FStar_List.split uu____6915 in
                               (match uu____6896 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7184 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7195 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7184, uu____7195)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7283) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7293) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7303,uu____7304) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7362 = let uu____7363 = env.tc_const c in N uu____7363 in
          (uu____7362, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7364 ->
          let uu____7379 =
            let uu____7380 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7380 in
          failwith uu____7379
      | FStar_Syntax_Syntax.Tm_type uu____7387 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7394 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7415 ->
          let uu____7424 =
            let uu____7425 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7425 in
          failwith uu____7424
      | FStar_Syntax_Syntax.Tm_uvar uu____7432 ->
          let uu____7453 =
            let uu____7454 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7454 in
          failwith uu____7453
      | FStar_Syntax_Syntax.Tm_delayed uu____7461 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7496 =
            let uu____7497 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7497 in
          failwith uu____7496
and mk_match:
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,(FStar_Syntax_Syntax.term',
                                                                 FStar_Syntax_Syntax.term')
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
          let uu____7550 = check_n env e0 in
          match uu____7550 with
          | (uu____7563,s_e0,u_e0) ->
              let uu____7566 =
                let uu____7599 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7668 = FStar_Syntax_Subst.open_branch b in
                       match uu____7668 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___118_7722 = env in
                             let uu____7723 =
                               let uu____7724 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7724 in
                             {
                               env = uu____7723;
                               subst = (uu___118_7722.subst);
                               tc_const = (uu___118_7722.tc_const)
                             } in
                           let uu____7727 = f env1 body in
                           (match uu____7727 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7815 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____7599 in
              (match uu____7566 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7933 = FStar_List.hd nms in
                     match uu____7933 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___101_7939  ->
                          match uu___101_7939 with
                          | M uu____7940 -> true
                          | uu____7941 -> false) nms in
                   let uu____7942 =
                     let uu____7983 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8083  ->
                              match uu____8083 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8290 =
                                         check env original_body (M t2) in
                                       (match uu____8290 with
                                        | (uu____8331,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8378,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____7983 in
                   (match uu____7942 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8592  ->
                                 match uu____8592 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8661 =
                                         let uu____8662 =
                                           let uu____8681 =
                                             let uu____8688 =
                                               let uu____8693 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____8694 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____8693, uu____8694) in
                                             [uu____8688] in
                                           (s_body, uu____8681) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8662 in
                                       mk1 uu____8661 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____8732 =
                              let uu____8733 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8733] in
                            let uu____8734 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____8732 uu____8734
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____8742 =
                              let uu____8749 =
                                let uu____8750 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8750 in
                              [uu____8749] in
                            let uu____8751 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____8742 uu____8751 in
                          let uu____8756 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____8815 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____8756, uu____8815)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____8838 =
                             let uu____8843 =
                               let uu____8844 =
                                 let uu____8879 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____8879,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8844 in
                             mk1 uu____8843 in
                           let uu____8932 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____8838, uu____8932))))
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
              let uu____8989 = FStar_Syntax_Syntax.mk_binder x in
              [uu____8989] in
            let uu____8990 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____8990 with
            | (x_binders1,e21) ->
                let uu____9003 = infer env e1 in
                (match uu____9003 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____9020 = is_C t1 in
                       if uu____9020
                       then
                         let uu___119_9021 = binding in
                         let uu____9022 =
                           let uu____9027 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____9027 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_9021.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_9021.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9022;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_9021.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_9021.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_9030 = env in
                       let uu____9031 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_9033 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_9033.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_9033.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9031;
                         subst = (uu___120_9030.subst);
                         tc_const = (uu___120_9030.tc_const)
                       } in
                     let uu____9034 = proceed env1 e21 in
                     (match uu____9034 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_9051 = binding in
                            let uu____9052 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_9051.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_9051.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9052;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_9051.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_9051.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____9057 =
                            let uu____9062 =
                              let uu____9063 =
                                let uu____9078 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_9088 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_9088.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_9088.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_9088.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_9088.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____9078) in
                              FStar_Syntax_Syntax.Tm_let uu____9063 in
                            mk1 uu____9062 in
                          let uu____9089 =
                            let uu____9094 =
                              let uu____9095 =
                                let uu____9110 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_9120 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_9120.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_9120.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_9120.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_9120.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9110) in
                              FStar_Syntax_Syntax.Tm_let uu____9095 in
                            mk1 uu____9094 in
                          (nm_rec, uu____9057, uu____9089))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_9133 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_9133.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_9133.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_9133.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_9135 = env in
                       let uu____9136 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_9138 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_9138.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_9138.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____9136;
                         subst = (uu___126_9135.subst);
                         tc_const = (uu___126_9135.tc_const)
                       } in
                     let uu____9139 = ensure_m env1 e21 in
                     (match uu____9139 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____9166 =
                              let uu____9167 =
                                let uu____9186 =
                                  let uu____9193 =
                                    let uu____9198 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____9199 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9198, uu____9199) in
                                  [uu____9193] in
                                (s_e2, uu____9186) in
                              FStar_Syntax_Syntax.Tm_app uu____9167 in
                            mk1 uu____9166 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____9220 =
                              let uu____9221 =
                                let uu____9240 =
                                  let uu____9247 =
                                    let uu____9252 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____9252) in
                                  [uu____9247] in
                                (s_e1, uu____9240) in
                              FStar_Syntax_Syntax.Tm_app uu____9221 in
                            mk1 uu____9220 in
                          let uu____9267 =
                            let uu____9268 =
                              let uu____9269 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9269] in
                            FStar_Syntax_Util.abs uu____9268 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____9270 =
                            let uu____9275 =
                              let uu____9276 =
                                let uu____9291 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_9301 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_9301.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_9301.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_9301.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_9301.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9291) in
                              FStar_Syntax_Syntax.Tm_let uu____9276 in
                            mk1 uu____9275 in
                          ((M t2), uu____9267, uu____9270)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9315 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____9315 in
      let uu____9316 = check env e mn in
      match uu____9316 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9332 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9354 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____9354 in
      let uu____9355 = check env e mn in
      match uu____9355 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9371 -> failwith "[check_m]: impossible"
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
        (let uu____9405 =
           let uu____9406 = is_C c in Prims.op_Negation uu____9406 in
         if uu____9405 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____9416 =
           let uu____9417 = FStar_Syntax_Subst.compress c in
           uu____9417.FStar_Syntax_Syntax.n in
         match uu____9416 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9452 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9452 with
              | (wp_head,wp_args) ->
                  ((let uu____9502 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9520 =
                           let uu____9521 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9521 in
                         Prims.op_Negation uu____9520) in
                    if uu____9502 then failwith "mismatch" else ());
                   (let uu____9531 =
                      let uu____9532 =
                        let uu____9551 =
                          FStar_List.map2
                            (fun uu____9579  ->
                               fun uu____9580  ->
                                 match (uu____9579, uu____9580) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9617 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9617
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9620 = print_implicit q in
                                         let uu____9621 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____9620 uu____9621)
                                      else ();
                                      (let uu____9623 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9623, q)))) args wp_args in
                        (head1, uu____9551) in
                      FStar_Syntax_Syntax.Tm_app uu____9532 in
                    mk1 uu____9531)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9663 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9663 with
              | (binders_orig,comp1) ->
                  let uu____9670 =
                    let uu____9685 =
                      FStar_List.map
                        (fun uu____9719  ->
                           match uu____9719 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9741 = is_C h in
                               if uu____9741
                               then
                                 let w' =
                                   let uu____9753 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9753 in
                                 let uu____9754 =
                                   let uu____9761 =
                                     let uu____9768 =
                                       let uu____9773 =
                                         let uu____9774 =
                                           let uu____9775 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____9775 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9774 in
                                       (uu____9773, q) in
                                     [uu____9768] in
                                   (w', q) :: uu____9761 in
                                 (w', uu____9754)
                               else
                                 (let x =
                                    let uu____9796 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9796 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9685 in
                  (match uu____9670 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____9851 =
                           let uu____9854 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9854 in
                         FStar_Syntax_Subst.subst_comp uu____9851 comp1 in
                       let app =
                         let uu____9860 =
                           let uu____9861 =
                             let uu____9880 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9895 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____9896 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9895, uu____9896)) bvs in
                             (wp, uu____9880) in
                           FStar_Syntax_Syntax.Tm_app uu____9861 in
                         mk1 uu____9860 in
                       let comp3 =
                         let uu____9904 = type_of_comp comp2 in
                         let uu____9905 = is_monadic_comp comp2 in
                         trans_G env uu____9904 uu____9905 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9907,uu____9908) ->
             trans_F_ env e wp
         | uu____9965 -> failwith "impossible trans_F_")
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
            let uu____9970 =
              let uu____9971 = star_type' env h in
              let uu____9976 =
                let uu____9987 =
                  let uu____9992 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____9992) in
                [uu____9987] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9971;
                FStar_Syntax_Syntax.effect_args = uu____9976;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____9970
          else
            (let uu____10002 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____10002)
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
    fun t  -> let uu____10017 = n env.env t in star_type' env uu____10017
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____10036 = n env.env t in check_n env uu____10036
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____10049 = n env.env c in
        let uu____10050 = n env.env wp in
        trans_F_ env uu____10049 uu____10050