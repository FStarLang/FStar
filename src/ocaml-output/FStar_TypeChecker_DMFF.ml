open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ;}[@@deriving show]
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
              let uu___298_93 = a in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___298_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___298_93.FStar_Syntax_Syntax.index);
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
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____151) -> t1
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
                | (sigelt,fv) ->
                    ((let uu____253 =
                        let uu____256 = FStar_ST.op_Bang sigelts in sigelt ::
                          uu____256 in
                      FStar_ST.op_Colon_Equals sigelts uu____253);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____418  ->
                     match uu____418 with
                     | (t,b) ->
                         let uu____429 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____429)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____460 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____460)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____483 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____483) in
              let uu____484 =
                let uu____499 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____521 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____521 in
                    let uu____524 =
                      let uu____525 =
                        let uu____532 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____533 =
                          let uu____536 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____536] in
                        uu____532 :: uu____533 in
                      FStar_List.append binders uu____525 in
                    FStar_Syntax_Util.abs uu____524 body
                      FStar_Pervasives_Native.None in
                  let uu____541 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____542 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____541, uu____542) in
                match uu____499 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____576 =
                        let uu____577 =
                          let uu____592 =
                            let uu____599 =
                              FStar_List.map
                                (fun uu____619  ->
                                   match uu____619 with
                                   | (bv,uu____629) ->
                                       let uu____630 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____631 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____630, uu____631)) binders in
                            let uu____632 =
                              let uu____639 =
                                let uu____644 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____645 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____644, uu____645) in
                              let uu____646 =
                                let uu____653 =
                                  let uu____658 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____658) in
                                [uu____653] in
                              uu____639 :: uu____646 in
                            FStar_List.append uu____599 uu____632 in
                          (fv, uu____592) in
                        FStar_Syntax_Syntax.Tm_app uu____577 in
                      mk1 uu____576 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____484 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____717 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____717 in
                    let ret1 =
                      let uu____721 =
                        let uu____722 =
                          let uu____725 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____725 in
                        FStar_Syntax_Util.residual_tot uu____722 in
                      FStar_Pervasives_Native.Some uu____721 in
                    let body =
                      let uu____727 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____727 ret1 in
                    let uu____728 =
                      let uu____729 = mk_all_implicit binders in
                      let uu____736 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____729 uu____736 in
                    FStar_Syntax_Util.abs uu____728 body ret1 in
                  let c_pure1 =
                    let uu____764 = mk_lid "pure" in
                    register env1 uu____764 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____769 =
                        let uu____770 =
                          let uu____771 =
                            let uu____778 =
                              let uu____779 =
                                let uu____780 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____780 in
                              FStar_Syntax_Syntax.mk_binder uu____779 in
                            [uu____778] in
                          let uu____781 =
                            let uu____784 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____784 in
                          FStar_Syntax_Util.arrow uu____771 uu____781 in
                        mk_gctx uu____770 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____769 in
                    let r =
                      let uu____786 =
                        let uu____787 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____787 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____786 in
                    let ret1 =
                      let uu____791 =
                        let uu____792 =
                          let uu____795 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____795 in
                        FStar_Syntax_Util.residual_tot uu____792 in
                      FStar_Pervasives_Native.Some uu____791 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____803 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____806 =
                          let uu____815 =
                            let uu____818 =
                              let uu____819 =
                                let uu____820 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____820
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____819 in
                            [uu____818] in
                          FStar_List.append gamma_as_args uu____815 in
                        FStar_Syntax_Util.mk_app uu____803 uu____806 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____823 =
                      let uu____824 = mk_all_implicit binders in
                      let uu____831 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____824 uu____831 in
                    FStar_Syntax_Util.abs uu____823 outer_body ret1 in
                  let c_app1 =
                    let uu____867 = mk_lid "app" in
                    register env1 uu____867 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____874 =
                        let uu____881 =
                          let uu____882 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____882 in
                        [uu____881] in
                      let uu____883 =
                        let uu____886 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____886 in
                      FStar_Syntax_Util.arrow uu____874 uu____883 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____889 =
                        let uu____890 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____890 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____889 in
                    let ret1 =
                      let uu____894 =
                        let uu____895 =
                          let uu____898 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____898 in
                        FStar_Syntax_Util.residual_tot uu____895 in
                      FStar_Pervasives_Native.Some uu____894 in
                    let uu____899 =
                      let uu____900 = mk_all_implicit binders in
                      let uu____907 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____900 uu____907 in
                    let uu____942 =
                      let uu____943 =
                        let uu____952 =
                          let uu____955 =
                            let uu____958 =
                              let uu____967 =
                                let uu____970 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____970] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____967 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____958 in
                          let uu____971 =
                            let uu____976 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____976] in
                          uu____955 :: uu____971 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____952 in
                      FStar_Syntax_Util.mk_app c_app1 uu____943 in
                    FStar_Syntax_Util.abs uu____899 uu____942 ret1 in
                  let c_lift11 =
                    let uu____980 = mk_lid "lift1" in
                    register env1 uu____980 c_lift1 in
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
                      let uu____988 =
                        let uu____995 =
                          let uu____996 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____996 in
                        let uu____997 =
                          let uu____1000 =
                            let uu____1001 =
                              FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____1001 in
                          [uu____1000] in
                        uu____995 :: uu____997 in
                      let uu____1002 =
                        let uu____1005 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1005 in
                      FStar_Syntax_Util.arrow uu____988 uu____1002 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1008 =
                        let uu____1009 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1009 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1008 in
                    let a2 =
                      let uu____1011 =
                        let uu____1012 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____1012 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1011 in
                    let ret1 =
                      let uu____1016 =
                        let uu____1017 =
                          let uu____1020 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____1020 in
                        FStar_Syntax_Util.residual_tot uu____1017 in
                      FStar_Pervasives_Native.Some uu____1016 in
                    let uu____1021 =
                      let uu____1022 = mk_all_implicit binders in
                      let uu____1029 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1022 uu____1029 in
                    let uu____1072 =
                      let uu____1073 =
                        let uu____1082 =
                          let uu____1085 =
                            let uu____1088 =
                              let uu____1097 =
                                let uu____1100 =
                                  let uu____1103 =
                                    let uu____1112 =
                                      let uu____1115 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1115] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1112 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1103 in
                                let uu____1116 =
                                  let uu____1121 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1121] in
                                uu____1100 :: uu____1116 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1097 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1088 in
                          let uu____1124 =
                            let uu____1129 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1129] in
                          uu____1085 :: uu____1124 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1082 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1073 in
                    FStar_Syntax_Util.abs uu____1021 uu____1072 ret1 in
                  let c_lift21 =
                    let uu____1133 = mk_lid "lift2" in
                    register env1 uu____1133 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1140 =
                        let uu____1147 =
                          let uu____1148 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1148 in
                        [uu____1147] in
                      let uu____1149 =
                        let uu____1152 =
                          let uu____1153 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1153 in
                        FStar_Syntax_Syntax.mk_Total uu____1152 in
                      FStar_Syntax_Util.arrow uu____1140 uu____1149 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1158 =
                        let uu____1159 =
                          let uu____1162 =
                            let uu____1163 =
                              let uu____1170 =
                                let uu____1171 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1171 in
                              [uu____1170] in
                            let uu____1172 =
                              let uu____1175 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1175 in
                            FStar_Syntax_Util.arrow uu____1163 uu____1172 in
                          mk_ctx uu____1162 in
                        FStar_Syntax_Util.residual_tot uu____1159 in
                      FStar_Pervasives_Native.Some uu____1158 in
                    let e1 =
                      let uu____1177 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1177 in
                    let body =
                      let uu____1179 =
                        let uu____1180 =
                          let uu____1187 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1187] in
                        FStar_List.append gamma uu____1180 in
                      let uu____1192 =
                        let uu____1193 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1196 =
                          let uu____1205 =
                            let uu____1206 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1206 in
                          let uu____1207 = args_of_binders1 gamma in
                          uu____1205 :: uu____1207 in
                        FStar_Syntax_Util.mk_app uu____1193 uu____1196 in
                      FStar_Syntax_Util.abs uu____1179 uu____1192 ret1 in
                    let uu____1210 =
                      let uu____1211 = mk_all_implicit binders in
                      let uu____1218 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1211 uu____1218 in
                    FStar_Syntax_Util.abs uu____1210 body ret1 in
                  let c_push1 =
                    let uu____1250 = mk_lid "push" in
                    register env1 uu____1250 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1270 =
                        let uu____1271 =
                          let uu____1286 = args_of_binders1 binders in
                          (c, uu____1286) in
                        FStar_Syntax_Syntax.Tm_app uu____1271 in
                      mk1 uu____1270
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1296 =
                        let uu____1297 =
                          let uu____1304 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1305 =
                            let uu____1308 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1308] in
                          uu____1304 :: uu____1305 in
                        let uu____1309 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1297 uu____1309 in
                      FStar_Syntax_Syntax.mk_Total uu____1296 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1313 =
                      let uu____1314 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1314 in
                    let uu____1325 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1327 =
                        let uu____1330 =
                          let uu____1339 =
                            let uu____1342 =
                              let uu____1345 =
                                let uu____1354 =
                                  let uu____1355 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1355 in
                                [uu____1354] in
                              FStar_Syntax_Util.mk_app l_ite uu____1345 in
                            [uu____1342] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1339 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1330 in
                      FStar_Syntax_Util.ascribe uu____1327
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1313 uu____1325
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1375 = mk_lid "wp_if_then_else" in
                    register env1 uu____1375 wp_if_then_else in
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
                      let uu____1386 =
                        let uu____1395 =
                          let uu____1398 =
                            let uu____1401 =
                              let uu____1410 =
                                let uu____1413 =
                                  let uu____1416 =
                                    let uu____1425 =
                                      let uu____1426 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1426 in
                                    [uu____1425] in
                                  FStar_Syntax_Util.mk_app l_and uu____1416 in
                                [uu____1413] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1410 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1401 in
                          let uu____1431 =
                            let uu____1436 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1436] in
                          uu____1398 :: uu____1431 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1395 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1386 in
                    let uu____1439 =
                      let uu____1440 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1440 in
                    FStar_Syntax_Util.abs uu____1439 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1452 = mk_lid "wp_assert" in
                    register env1 uu____1452 wp_assert in
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
                      let uu____1463 =
                        let uu____1472 =
                          let uu____1475 =
                            let uu____1478 =
                              let uu____1487 =
                                let uu____1490 =
                                  let uu____1493 =
                                    let uu____1502 =
                                      let uu____1503 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1503 in
                                    [uu____1502] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1493 in
                                [uu____1490] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1487 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1478 in
                          let uu____1508 =
                            let uu____1513 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1513] in
                          uu____1475 :: uu____1508 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1472 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1463 in
                    let uu____1516 =
                      let uu____1517 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1517 in
                    FStar_Syntax_Util.abs uu____1516 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1529 = mk_lid "wp_assume" in
                    register env1 uu____1529 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1538 =
                        let uu____1545 =
                          let uu____1546 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1546 in
                        [uu____1545] in
                      let uu____1547 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1538 uu____1547 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1554 =
                        let uu____1563 =
                          let uu____1566 =
                            let uu____1569 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1569 in
                          let uu____1578 =
                            let uu____1583 =
                              let uu____1586 =
                                let uu____1595 =
                                  let uu____1598 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1598] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1595 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1586 in
                            [uu____1583] in
                          uu____1566 :: uu____1578 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1563 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1554 in
                    let uu____1605 =
                      let uu____1606 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1606 in
                    FStar_Syntax_Util.abs uu____1605 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1618 = mk_lid "wp_close" in
                    register env1 uu____1618 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1628 =
                      let uu____1629 =
                        let uu____1630 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1630 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1629 in
                    FStar_Pervasives_Native.Some uu____1628 in
                  let mk_forall1 x body =
                    let uu____1642 =
                      let uu____1645 =
                        let uu____1646 =
                          let uu____1661 =
                            let uu____1664 =
                              let uu____1665 =
                                let uu____1666 =
                                  let uu____1667 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1667] in
                                FStar_Syntax_Util.abs uu____1666 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1665 in
                            [uu____1664] in
                          (FStar_Syntax_Util.tforall, uu____1661) in
                        FStar_Syntax_Syntax.Tm_app uu____1646 in
                      FStar_Syntax_Syntax.mk uu____1645 in
                    uu____1642 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1677 =
                      let uu____1678 = FStar_Syntax_Subst.compress t in
                      uu____1678.FStar_Syntax_Syntax.n in
                    match uu____1677 with
                    | FStar_Syntax_Syntax.Tm_type uu____1681 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1707  ->
                              match uu____1707 with
                              | (b,uu____1713) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1714 -> true in
                  let rec is_monotonic t =
                    let uu____1719 =
                      let uu____1720 = FStar_Syntax_Subst.compress t in
                      uu____1720.FStar_Syntax_Syntax.n in
                    match uu____1719 with
                    | FStar_Syntax_Syntax.Tm_type uu____1723 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1749  ->
                              match uu____1749 with
                              | (b,uu____1755) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1756 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1808 =
                      let uu____1809 = FStar_Syntax_Subst.compress t1 in
                      uu____1809.FStar_Syntax_Syntax.n in
                    match uu____1808 with
                    | FStar_Syntax_Syntax.Tm_type uu____1812 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1815);
                                      FStar_Syntax_Syntax.pos = uu____1816;
                                      FStar_Syntax_Syntax.vars = uu____1817;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1851 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1851
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1854 =
                              let uu____1857 =
                                let uu____1866 =
                                  let uu____1867 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1867 in
                                [uu____1866] in
                              FStar_Syntax_Util.mk_app x uu____1857 in
                            let uu____1868 =
                              let uu____1871 =
                                let uu____1880 =
                                  let uu____1881 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1881 in
                                [uu____1880] in
                              FStar_Syntax_Util.mk_app y uu____1871 in
                            mk_rel1 b uu____1854 uu____1868 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1886 =
                               let uu____1887 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1890 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1887 uu____1890 in
                             let uu____1893 =
                               let uu____1894 =
                                 let uu____1897 =
                                   let uu____1906 =
                                     let uu____1907 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1907 in
                                   [uu____1906] in
                                 FStar_Syntax_Util.mk_app x uu____1897 in
                               let uu____1908 =
                                 let uu____1911 =
                                   let uu____1920 =
                                     let uu____1921 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1921 in
                                   [uu____1920] in
                                 FStar_Syntax_Util.mk_app y uu____1911 in
                               mk_rel1 b uu____1894 uu____1908 in
                             FStar_Syntax_Util.mk_imp uu____1886 uu____1893 in
                           let uu____1922 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1922)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1925);
                                      FStar_Syntax_Syntax.pos = uu____1926;
                                      FStar_Syntax_Syntax.vars = uu____1927;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1961 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1961
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1964 =
                              let uu____1967 =
                                let uu____1976 =
                                  let uu____1977 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1977 in
                                [uu____1976] in
                              FStar_Syntax_Util.mk_app x uu____1967 in
                            let uu____1978 =
                              let uu____1981 =
                                let uu____1990 =
                                  let uu____1991 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1991 in
                                [uu____1990] in
                              FStar_Syntax_Util.mk_app y uu____1981 in
                            mk_rel1 b uu____1964 uu____1978 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1996 =
                               let uu____1997 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2000 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1997 uu____2000 in
                             let uu____2003 =
                               let uu____2004 =
                                 let uu____2007 =
                                   let uu____2016 =
                                     let uu____2017 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2017 in
                                   [uu____2016] in
                                 FStar_Syntax_Util.mk_app x uu____2007 in
                               let uu____2018 =
                                 let uu____2021 =
                                   let uu____2030 =
                                     let uu____2031 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2031 in
                                   [uu____2030] in
                                 FStar_Syntax_Util.mk_app y uu____2021 in
                               mk_rel1 b uu____2004 uu____2018 in
                             FStar_Syntax_Util.mk_imp uu____1996 uu____2003 in
                           let uu____2032 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2032)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___299_2063 = t1 in
                          let uu____2064 =
                            let uu____2065 =
                              let uu____2078 =
                                let uu____2079 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2079 in
                              ([binder], uu____2078) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2065 in
                          {
                            FStar_Syntax_Syntax.n = uu____2064;
                            FStar_Syntax_Syntax.pos =
                              (uu___299_2063.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___299_2063.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2094 ->
                        failwith "unhandled arrow"
                    | uu____2107 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2122 =
                        let uu____2123 = FStar_Syntax_Subst.compress t1 in
                        uu____2123.FStar_Syntax_Syntax.n in
                      match uu____2122 with
                      | FStar_Syntax_Syntax.Tm_type uu____2126 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2149 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2149
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2164 =
                                let uu____2165 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2165 i in
                              FStar_Syntax_Syntax.fvar uu____2164
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2192 =
                            let uu____2199 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2213  ->
                                     match uu____2213 with
                                     | (t2,q) ->
                                         let uu____2220 = project i x in
                                         let uu____2221 = project i y in
                                         mk_stronger t2 uu____2220 uu____2221)
                                args in
                            match uu____2199 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2192 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2248);
                                      FStar_Syntax_Syntax.pos = uu____2249;
                                      FStar_Syntax_Syntax.vars = uu____2250;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2288  ->
                                   match uu____2288 with
                                   | (bv,q) ->
                                       let uu____2295 =
                                         let uu____2296 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2296 in
                                       FStar_Syntax_Syntax.gen_bv uu____2295
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2303 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2303) bvs in
                          let body =
                            let uu____2305 = FStar_Syntax_Util.mk_app x args in
                            let uu____2306 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2305 uu____2306 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2313);
                                      FStar_Syntax_Syntax.pos = uu____2314;
                                      FStar_Syntax_Syntax.vars = uu____2315;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2353  ->
                                   match uu____2353 with
                                   | (bv,q) ->
                                       let uu____2360 =
                                         let uu____2361 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2361 in
                                       FStar_Syntax_Syntax.gen_bv uu____2360
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2368 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2368) bvs in
                          let body =
                            let uu____2370 = FStar_Syntax_Util.mk_app x args in
                            let uu____2371 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2370 uu____2371 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2376 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2378 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2379 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2380 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2378 uu____2379 uu____2380 in
                    let uu____2381 =
                      let uu____2382 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2382 in
                    FStar_Syntax_Util.abs uu____2381 body ret_tot_type in
                  let stronger1 =
                    let uu____2410 = mk_lid "stronger" in
                    register env1 uu____2410 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2416 = FStar_Util.prefix gamma in
                    match uu____2416 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2461 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2461 in
                          let uu____2464 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2464 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2474 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2474 in
                              let guard_free1 =
                                let uu____2484 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2484 in
                              let pat =
                                let uu____2488 =
                                  let uu____2497 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2497] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2488 in
                              let pattern_guarded_body =
                                let uu____2501 =
                                  let uu____2502 =
                                    let uu____2509 =
                                      let uu____2510 =
                                        let uu____2521 =
                                          let uu____2524 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2524] in
                                        [uu____2521] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2510 in
                                    (body, uu____2509) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2502 in
                                mk1 uu____2501 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2529 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2533 =
                            let uu____2534 =
                              let uu____2535 =
                                let uu____2536 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2539 =
                                  let uu____2548 = args_of_binders1 wp_args in
                                  let uu____2551 =
                                    let uu____2554 =
                                      let uu____2555 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2555 in
                                    [uu____2554] in
                                  FStar_List.append uu____2548 uu____2551 in
                                FStar_Syntax_Util.mk_app uu____2536
                                  uu____2539 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2535 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2534 in
                          FStar_Syntax_Util.abs gamma uu____2533
                            ret_gtot_type in
                        let uu____2556 =
                          let uu____2557 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2557 in
                        FStar_Syntax_Util.abs uu____2556 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2569 = mk_lid "wp_ite" in
                    register env1 uu____2569 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2575 = FStar_Util.prefix gamma in
                    match uu____2575 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2618 =
                            let uu____2619 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2622 =
                              let uu____2631 =
                                let uu____2632 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2632 in
                              [uu____2631] in
                            FStar_Syntax_Util.mk_app uu____2619 uu____2622 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2618 in
                        let uu____2633 =
                          let uu____2634 =
                            let uu____2641 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2641 gamma in
                          FStar_List.append binders uu____2634 in
                        FStar_Syntax_Util.abs uu____2633 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2657 = mk_lid "null_wp" in
                    register env1 uu____2657 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2666 =
                        let uu____2675 =
                          let uu____2678 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2679 =
                            let uu____2682 =
                              let uu____2685 =
                                let uu____2694 =
                                  let uu____2695 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2695 in
                                [uu____2694] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2685 in
                            let uu____2696 =
                              let uu____2701 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2701] in
                            uu____2682 :: uu____2696 in
                          uu____2678 :: uu____2679 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2675 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2666 in
                    let uu____2704 =
                      let uu____2705 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2705 in
                    FStar_Syntax_Util.abs uu____2704 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2717 = mk_lid "wp_trivial" in
                    register env1 uu____2717 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2722 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2722
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2727 =
                      let uu____2730 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____2730 in
                    let uu____2799 =
                      let uu___300_2800 = ed in
                      let uu____2801 =
                        let uu____2802 = c wp_if_then_else2 in
                        ([], uu____2802) in
                      let uu____2805 =
                        let uu____2806 = c wp_ite2 in ([], uu____2806) in
                      let uu____2809 =
                        let uu____2810 = c stronger2 in ([], uu____2810) in
                      let uu____2813 =
                        let uu____2814 = c wp_close2 in ([], uu____2814) in
                      let uu____2817 =
                        let uu____2818 = c wp_assert2 in ([], uu____2818) in
                      let uu____2821 =
                        let uu____2822 = c wp_assume2 in ([], uu____2822) in
                      let uu____2825 =
                        let uu____2826 = c null_wp2 in ([], uu____2826) in
                      let uu____2829 =
                        let uu____2830 = c wp_trivial2 in ([], uu____2830) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___300_2800.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___300_2800.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___300_2800.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___300_2800.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___300_2800.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___300_2800.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___300_2800.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2801;
                        FStar_Syntax_Syntax.ite_wp = uu____2805;
                        FStar_Syntax_Syntax.stronger = uu____2809;
                        FStar_Syntax_Syntax.close_wp = uu____2813;
                        FStar_Syntax_Syntax.assert_p = uu____2817;
                        FStar_Syntax_Syntax.assume_p = uu____2821;
                        FStar_Syntax_Syntax.null_wp = uu____2825;
                        FStar_Syntax_Syntax.trivial = uu____2829;
                        FStar_Syntax_Syntax.repr =
                          (uu___300_2800.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___300_2800.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___300_2800.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___300_2800.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2727, uu____2799)))))
type env_ = env[@@deriving show]
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___301_2844 = dmff_env in
      {
        env = env';
        subst = (uu___301_2844.subst);
        tc_const = (uu___301_2844.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ[@@deriving show]
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2857 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2869 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm[@@deriving show]
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___287_2879  ->
    match uu___287_2879 with
    | FStar_Syntax_Syntax.Total (t,uu____2881) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___286_2894  ->
                match uu___286_2894 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2895 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2897 =
          let uu____2898 =
            let uu____2899 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2899 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2898 in
        failwith uu____2897
    | FStar_Syntax_Syntax.GTotal uu____2900 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___288_2911  ->
    match uu___288_2911 with
    | N t ->
        let uu____2913 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2913
    | M t ->
        let uu____2915 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2915
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2919,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2921;
                      FStar_Syntax_Syntax.vars = uu____2922;_})
        -> nm_of_comp n2
    | uu____2939 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____2947 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____2947 with | M uu____2948 -> true | N uu____2949 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2953 -> false
let double_star: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ  ->
    let star_once typ1 =
      let uu____2963 =
        let uu____2970 =
          let uu____2971 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2971 in
        [uu____2970] in
      let uu____2972 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2963 uu____2972 in
    let uu____2975 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2975
let rec mk_star_to_type:
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        mk1
          (let uu____3012 =
             let uu____3025 =
               let uu____3032 =
                 let uu____3037 =
                   let uu____3038 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____3038 in
                 let uu____3039 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____3037, uu____3039) in
               [uu____3032] in
             let uu____3048 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____3025, uu____3048) in
           FStar_Syntax_Syntax.Tm_arrow uu____3012)
and star_type':
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk1 in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3076) ->
          let binders1 =
            FStar_List.map
              (fun uu____3112  ->
                 match uu____3112 with
                 | (bv,aqual) ->
                     let uu____3123 =
                       let uu___302_3124 = bv in
                       let uu____3125 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___302_3124.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___302_3124.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3125
                       } in
                     (uu____3123, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3128,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3130);
                             FStar_Syntax_Syntax.pos = uu____3131;
                             FStar_Syntax_Syntax.vars = uu____3132;_})
               ->
               let uu____3157 =
                 let uu____3158 =
                   let uu____3171 =
                     let uu____3172 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3172 in
                   (binders1, uu____3171) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3158 in
               mk1 uu____3157
           | uu____3179 ->
               let uu____3180 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3180 with
                | N hn ->
                    let uu____3182 =
                      let uu____3183 =
                        let uu____3196 =
                          let uu____3197 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3197 in
                        (binders1, uu____3196) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3183 in
                    mk1 uu____3182
                | M a ->
                    let uu____3205 =
                      let uu____3206 =
                        let uu____3219 =
                          let uu____3226 =
                            let uu____3233 =
                              let uu____3238 =
                                let uu____3239 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3239 in
                              let uu____3240 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3238, uu____3240) in
                            [uu____3233] in
                          FStar_List.append binders1 uu____3226 in
                        let uu____3253 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3219, uu____3253) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3206 in
                    mk1 uu____3205))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3323 = f x in
                    FStar_Util.string_builder_append strb uu____3323);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3330 = f x1 in
                         FStar_Util.string_builder_append strb uu____3330))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3332 =
              let uu____3337 =
                let uu____3338 = FStar_Syntax_Print.term_to_string t2 in
                let uu____3339 =
                  string_of_set FStar_Syntax_Print.bv_to_string s in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3338 uu____3339 in
              (FStar_Errors.Warning_DependencyFound, uu____3337) in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3332 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3347 =
              let uu____3348 = FStar_Syntax_Subst.compress ty in
              uu____3348.FStar_Syntax_Syntax.n in
            match uu____3347 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3369 =
                  let uu____3370 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3370 in
                if uu____3369
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3396 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3396 s in
                       let uu____3399 =
                         let uu____3400 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3400 in
                       if uu____3399
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else () in
                     let uu____3403 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3403 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3425  ->
                                  match uu____3425 with
                                  | (bv,uu____3435) ->
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
            | uu____3449 ->
                ((let uu____3451 =
                    let uu____3456 =
                      let uu____3457 = FStar_Syntax_Print.term_to_string ty in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3457 in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3456) in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3451);
                 false) in
          let rec is_valid_application head2 =
            let uu____3462 =
              let uu____3463 = FStar_Syntax_Subst.compress head2 in
              uu____3463.FStar_Syntax_Syntax.n in
            match uu____3462 with
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
                  (let uu____3468 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3468)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3470 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3470 with
                 | ((uu____3479,ty),uu____3481) ->
                     let uu____3486 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3486
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3494 -> true
                        | uu____3509 ->
                            ((let uu____3511 =
                                let uu____3516 =
                                  let uu____3517 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3517 in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3516) in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3511);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3519 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3520 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3522) ->
                is_valid_application t2
            | uu____3527 -> false in
          let uu____3528 = is_valid_application head1 in
          if uu____3528
          then
            let uu____3529 =
              let uu____3530 =
                let uu____3545 =
                  FStar_List.map
                    (fun uu____3566  ->
                       match uu____3566 with
                       | (t2,qual) ->
                           let uu____3583 = star_type' env t2 in
                           (uu____3583, qual)) args in
                (head1, uu____3545) in
              FStar_Syntax_Syntax.Tm_app uu____3530 in
            mk1 uu____3529
          else
            (let uu____3593 =
               let uu____3598 =
                 let uu____3599 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3599 in
               (FStar_Errors.Fatal_WrongTerm, uu____3598) in
             FStar_Errors.raise_err uu____3593)
      | FStar_Syntax_Syntax.Tm_bvar uu____3600 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3601 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3602 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3603 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3627 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3627 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___305_3635 = env in
                 let uu____3636 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3636;
                   subst = (uu___305_3635.subst);
                   tc_const = (uu___305_3635.tc_const)
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
               ((let uu___306_3656 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___306_3656.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___306_3656.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3663 =
            let uu____3664 =
              let uu____3671 = star_type' env t2 in (uu____3671, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3664 in
          mk1 uu____3663
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3719 =
            let uu____3720 =
              let uu____3747 = star_type' env e in
              let uu____3748 =
                let uu____3763 =
                  let uu____3770 = star_type' env t2 in
                  FStar_Util.Inl uu____3770 in
                (uu____3763, FStar_Pervasives_Native.None) in
              (uu____3747, uu____3748, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3720 in
          mk1 uu____3719
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3848 =
            let uu____3849 =
              let uu____3876 = star_type' env e in
              let uu____3877 =
                let uu____3892 =
                  let uu____3899 =
                    star_type' env (FStar_Syntax_Util.comp_result c) in
                  FStar_Util.Inl uu____3899 in
                (uu____3892, FStar_Pervasives_Native.None) in
              (uu____3876, uu____3877, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3849 in
          mk1 uu____3848
      | FStar_Syntax_Syntax.Tm_refine uu____3930 ->
          let uu____3937 =
            let uu____3942 =
              let uu____3943 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3943 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3942) in
          FStar_Errors.raise_err uu____3937
      | FStar_Syntax_Syntax.Tm_uinst uu____3944 ->
          let uu____3951 =
            let uu____3956 =
              let uu____3957 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3957 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3956) in
          FStar_Errors.raise_err uu____3951
      | FStar_Syntax_Syntax.Tm_constant uu____3958 ->
          let uu____3959 =
            let uu____3964 =
              let uu____3965 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3965 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3964) in
          FStar_Errors.raise_err uu____3959
      | FStar_Syntax_Syntax.Tm_match uu____3966 ->
          let uu____3989 =
            let uu____3994 =
              let uu____3995 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3995 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3994) in
          FStar_Errors.raise_err uu____3989
      | FStar_Syntax_Syntax.Tm_let uu____3996 ->
          let uu____4009 =
            let uu____4014 =
              let uu____4015 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4015 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4014) in
          FStar_Errors.raise_err uu____4009
      | FStar_Syntax_Syntax.Tm_uvar uu____4016 ->
          let uu____4033 =
            let uu____4038 =
              let uu____4039 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4039 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4038) in
          FStar_Errors.raise_err uu____4033
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4040 =
            let uu____4045 =
              let uu____4046 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4046 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4045) in
          FStar_Errors.raise_err uu____4040
      | FStar_Syntax_Syntax.Tm_delayed uu____4047 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___290_4076  ->
    match uu___290_4076 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___289_4083  ->
                match uu___289_4083 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4084 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____4088 =
      let uu____4089 = FStar_Syntax_Subst.compress t in
      uu____4089.FStar_Syntax_Syntax.n in
    match uu____4088 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4115 =
            let uu____4116 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____4116 in
          is_C uu____4115 in
        if r
        then
          ((let uu____4132 =
              let uu____4133 =
                FStar_List.for_all
                  (fun uu____4141  ->
                     match uu____4141 with | (h,uu____4147) -> is_C h) args in
              Prims.op_Negation uu____4133 in
            if uu____4132 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4151 =
              let uu____4152 =
                FStar_List.for_all
                  (fun uu____4161  ->
                     match uu____4161 with
                     | (h,uu____4167) ->
                         let uu____4168 = is_C h in
                         Prims.op_Negation uu____4168) args in
              Prims.op_Negation uu____4152 in
            if uu____4151 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4188 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4188 with
         | M t1 ->
             ((let uu____4191 = is_C t1 in
               if uu____4191 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4195) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4201) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4207,uu____4208) -> is_C t1
    | uu____4249 -> false
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
          let uu____4272 =
            let uu____4273 =
              let uu____4288 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4289 =
                let uu____4296 =
                  let uu____4301 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4301) in
                [uu____4296] in
              (uu____4288, uu____4289) in
            FStar_Syntax_Syntax.Tm_app uu____4273 in
          mk1 uu____4272 in
        let uu____4316 =
          let uu____4317 = FStar_Syntax_Syntax.mk_binder p in [uu____4317] in
        FStar_Syntax_Util.abs uu____4316 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___291_4320  ->
    match uu___291_4320 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4321 -> false
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
        let return_if uu____4496 =
          match uu____4496 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4523 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4525 =
                       let uu____4526 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4526 in
                     Prims.op_Negation uu____4525) in
                if uu____4523
                then
                  let uu____4527 =
                    let uu____4532 =
                      let uu____4533 = FStar_Syntax_Print.term_to_string e in
                      let uu____4534 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4535 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4533 uu____4534 uu____4535 in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4532) in
                  FStar_Errors.raise_err uu____4527
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4552 = mk_return env t1 s_e in
                     ((M t1), uu____4552, u_e)))
               | (M t1,N t2) ->
                   let uu____4555 =
                     let uu____4560 =
                       let uu____4561 = FStar_Syntax_Print.term_to_string e in
                       let uu____4562 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4563 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4561 uu____4562 uu____4563 in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4560) in
                   FStar_Errors.raise_err uu____4555) in
        let ensure_m env1 e2 =
          let strip_m uu___292_4604 =
            match uu___292_4604 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4620 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4640 =
                let uu____4645 =
                  let uu____4646 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4646 in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4645) in
              FStar_Errors.raise_error uu____4640 e2.FStar_Syntax_Syntax.pos
          | M uu____4653 ->
              let uu____4654 = check env1 e2 context_nm in strip_m uu____4654 in
        let uu____4661 =
          let uu____4662 = FStar_Syntax_Subst.compress e in
          uu____4662.FStar_Syntax_Syntax.n in
        match uu____4661 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4671 ->
            let uu____4672 = infer env e in return_if uu____4672
        | FStar_Syntax_Syntax.Tm_name uu____4679 ->
            let uu____4680 = infer env e in return_if uu____4680
        | FStar_Syntax_Syntax.Tm_fvar uu____4687 ->
            let uu____4688 = infer env e in return_if uu____4688
        | FStar_Syntax_Syntax.Tm_abs uu____4695 ->
            let uu____4712 = infer env e in return_if uu____4712
        | FStar_Syntax_Syntax.Tm_constant uu____4719 ->
            let uu____4720 = infer env e in return_if uu____4720
        | FStar_Syntax_Syntax.Tm_app uu____4727 ->
            let uu____4742 = infer env e in return_if uu____4742
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4810) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4816) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4822,uu____4823) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4864 ->
            let uu____4877 =
              let uu____4878 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4878 in
            failwith uu____4877
        | FStar_Syntax_Syntax.Tm_type uu____4885 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4892 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4911 ->
            let uu____4918 =
              let uu____4919 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4919 in
            failwith uu____4918
        | FStar_Syntax_Syntax.Tm_uvar uu____4926 ->
            let uu____4943 =
              let uu____4944 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4944 in
            failwith uu____4943
        | FStar_Syntax_Syntax.Tm_delayed uu____4951 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4982 =
              let uu____4983 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4983 in
            failwith uu____4982
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
      let uu____5007 =
        let uu____5008 = FStar_Syntax_Subst.compress e in
        uu____5008.FStar_Syntax_Syntax.n in
      match uu____5007 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5067;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5068;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5074 =
                  let uu___307_5075 = rc in
                  let uu____5076 =
                    let uu____5081 =
                      let uu____5082 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____5082 in
                    FStar_Pervasives_Native.Some uu____5081 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___307_5075.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5076;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___307_5075.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____5074 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___308_5092 = env in
            let uu____5093 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____5093;
              subst = (uu___308_5092.subst);
              tc_const = (uu___308_5092.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____5113  ->
                 match uu____5113 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___309_5126 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___309_5126.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___309_5126.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____5127 =
            FStar_List.fold_left
              (fun uu____5156  ->
                 fun uu____5157  ->
                   match (uu____5156, uu____5157) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5205 = is_C c in
                       if uu____5205
                       then
                         let xw =
                           let uu____5213 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5213 in
                         let x =
                           let uu___310_5215 = bv in
                           let uu____5216 =
                             let uu____5219 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5219 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___310_5215.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___310_5215.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5216
                           } in
                         let env3 =
                           let uu___311_5221 = env2 in
                           let uu____5222 =
                             let uu____5225 =
                               let uu____5226 =
                                 let uu____5233 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5233) in
                               FStar_Syntax_Syntax.NT uu____5226 in
                             uu____5225 :: (env2.subst) in
                           {
                             env = (uu___311_5221.env);
                             subst = uu____5222;
                             tc_const = (uu___311_5221.tc_const)
                           } in
                         let uu____5234 =
                           let uu____5237 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5238 =
                             let uu____5241 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5241 :: acc in
                           uu____5237 :: uu____5238 in
                         (env3, uu____5234)
                       else
                         (let x =
                            let uu___312_5246 = bv in
                            let uu____5247 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___312_5246.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___312_5246.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5247
                            } in
                          let uu____5250 =
                            let uu____5253 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5253 :: acc in
                          (env2, uu____5250))) (env1, []) binders1 in
          (match uu____5127 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5273 =
                 let check_what =
                   let uu____5291 = is_monadic rc_opt1 in
                   if uu____5291 then check_m else check_n in
                 let uu____5303 = check_what env2 body1 in
                 match uu____5303 with
                 | (t,s_body,u_body) ->
                     let uu____5319 =
                       let uu____5320 =
                         let uu____5321 = is_monadic rc_opt1 in
                         if uu____5321 then M t else N t in
                       comp_of_nm uu____5320 in
                     (uu____5319, s_body, u_body) in
               (match uu____5273 with
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
                                 let uu____5346 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___293_5350  ->
                                           match uu___293_5350 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5351 -> false)) in
                                 if uu____5346
                                 then
                                   let uu____5352 =
                                     FStar_List.filter
                                       (fun uu___294_5356  ->
                                          match uu___294_5356 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5357 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5352
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5366 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___295_5370  ->
                                         match uu___295_5370 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5371 -> false)) in
                               if uu____5366
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___296_5378  ->
                                        match uu___296_5378 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5379 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5380 =
                                   let uu____5381 =
                                     let uu____5386 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5386 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5381 flags1 in
                                 FStar_Pervasives_Native.Some uu____5380
                               else
                                 (let uu____5388 =
                                    let uu___313_5389 = rc in
                                    let uu____5390 =
                                      let uu____5395 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5395 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___313_5389.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5390;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___313_5389.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5388)) in
                    let uu____5396 =
                      let comp1 =
                        let uu____5406 = is_monadic rc_opt1 in
                        let uu____5407 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5406 uu____5407 in
                      let uu____5408 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5408,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5396 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5450 =
                             let uu____5451 =
                               let uu____5468 =
                                 let uu____5471 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5471 s_rc_opt in
                               (s_binders1, s_body1, uu____5468) in
                             FStar_Syntax_Syntax.Tm_abs uu____5451 in
                           mk1 uu____5450 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5481 =
                             let uu____5482 =
                               let uu____5499 =
                                 let uu____5502 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5502 u_rc_opt in
                               (u_binders2, u_body2, uu____5499) in
                             FStar_Syntax_Syntax.Tm_abs uu____5482 in
                           mk1 uu____5481 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5512;_};
            FStar_Syntax_Syntax.fv_delta = uu____5513;
            FStar_Syntax_Syntax.fv_qual = uu____5514;_}
          ->
          let uu____5517 =
            let uu____5522 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5522 in
          (match uu____5517 with
           | (uu____5553,t) ->
               let uu____5555 = let uu____5556 = normalize1 t in N uu____5556 in
               (uu____5555, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5557;
             FStar_Syntax_Syntax.vars = uu____5558;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5621 = FStar_Syntax_Util.head_and_args e in
          (match uu____5621 with
           | (unary_op,uu____5643) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5702;
             FStar_Syntax_Syntax.vars = uu____5703;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5779 = FStar_Syntax_Util.head_and_args e in
          (match uu____5779 with
           | (unary_op,uu____5801) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5866;
             FStar_Syntax_Syntax.vars = uu____5867;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____5905 = infer env a in
          (match uu____5905 with
           | (t,s,u) ->
               let uu____5921 = FStar_Syntax_Util.head_and_args e in
               (match uu____5921 with
                | (head1,uu____5943) ->
                    let uu____5964 =
                      let uu____5965 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____5965 in
                    let uu____5966 =
                      let uu____5969 =
                        let uu____5970 =
                          let uu____5985 =
                            let uu____5988 = FStar_Syntax_Syntax.as_arg s in
                            [uu____5988] in
                          (head1, uu____5985) in
                        FStar_Syntax_Syntax.Tm_app uu____5970 in
                      mk1 uu____5969 in
                    let uu____5993 =
                      let uu____5996 =
                        let uu____5997 =
                          let uu____6012 =
                            let uu____6015 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6015] in
                          (head1, uu____6012) in
                        FStar_Syntax_Syntax.Tm_app uu____5997 in
                      mk1 uu____5996 in
                    (uu____5964, uu____5966, uu____5993)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6024;
             FStar_Syntax_Syntax.vars = uu____6025;_},(a1,uu____6027)::a2::[])
          ->
          let uu____6069 = infer env a1 in
          (match uu____6069 with
           | (t,s,u) ->
               let uu____6085 = FStar_Syntax_Util.head_and_args e in
               (match uu____6085 with
                | (head1,uu____6107) ->
                    let uu____6128 =
                      let uu____6131 =
                        let uu____6132 =
                          let uu____6147 =
                            let uu____6150 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6150; a2] in
                          (head1, uu____6147) in
                        FStar_Syntax_Syntax.Tm_app uu____6132 in
                      mk1 uu____6131 in
                    let uu____6167 =
                      let uu____6170 =
                        let uu____6171 =
                          let uu____6186 =
                            let uu____6189 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6189; a2] in
                          (head1, uu____6186) in
                        FStar_Syntax_Syntax.Tm_app uu____6171 in
                      mk1 uu____6170 in
                    (t, uu____6128, uu____6167)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6210;
             FStar_Syntax_Syntax.vars = uu____6211;_},uu____6212)
          ->
          let uu____6233 =
            let uu____6238 =
              let uu____6239 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6239 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6238) in
          FStar_Errors.raise_error uu____6233 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6246;
             FStar_Syntax_Syntax.vars = uu____6247;_},uu____6248)
          ->
          let uu____6269 =
            let uu____6274 =
              let uu____6275 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6275 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6274) in
          FStar_Errors.raise_error uu____6269 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6304 = check_n env head1 in
          (match uu____6304 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6324 =
                   let uu____6325 = FStar_Syntax_Subst.compress t in
                   uu____6325.FStar_Syntax_Syntax.n in
                 match uu____6324 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6328 -> true
                 | uu____6341 -> false in
               let rec flatten1 t =
                 let uu____6358 =
                   let uu____6359 = FStar_Syntax_Subst.compress t in
                   uu____6359.FStar_Syntax_Syntax.n in
                 match uu____6358 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6376);
                                FStar_Syntax_Syntax.pos = uu____6377;
                                FStar_Syntax_Syntax.vars = uu____6378;_})
                     when is_arrow t1 ->
                     let uu____6403 = flatten1 t1 in
                     (match uu____6403 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6485,uu____6486)
                     -> flatten1 e1
                 | uu____6527 ->
                     let uu____6528 =
                       let uu____6533 =
                         let uu____6534 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6534 in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6533) in
                     FStar_Errors.raise_err uu____6528 in
               let uu____6547 = flatten1 t_head in
               (match uu____6547 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6607 =
                          let uu____6612 =
                            let uu____6613 = FStar_Util.string_of_int n1 in
                            let uu____6620 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____6631 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6613 uu____6620 uu____6631 in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6612) in
                        FStar_Errors.raise_err uu____6607)
                     else ();
                     (let uu____6639 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____6639 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6680 args1 =
                            match uu____6680 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6754 =
                                       let uu____6755 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____6755.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____6754
                                 | (binders3,[]) ->
                                     let uu____6785 =
                                       let uu____6786 =
                                         let uu____6789 =
                                           let uu____6790 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6790 in
                                         FStar_Syntax_Subst.compress
                                           uu____6789 in
                                       uu____6786.FStar_Syntax_Syntax.n in
                                     (match uu____6785 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6815 =
                                            let uu____6816 =
                                              let uu____6817 =
                                                let uu____6830 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____6830) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6817 in
                                            mk1 uu____6816 in
                                          N uu____6815
                                      | uu____6837 -> failwith "wat?")
                                 | ([],uu____6838::uu____6839) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6879)::binders3,(arg,uu____6882)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____6935 = FStar_List.splitAt n' binders1 in
                          (match uu____6935 with
                           | (binders2,uu____6967) ->
                               let uu____6992 =
                                 let uu____7011 =
                                   FStar_List.map2
                                     (fun uu____7059  ->
                                        fun uu____7060  ->
                                          match (uu____7059, uu____7060) with
                                          | ((bv,uu____7092),(arg,q)) ->
                                              let uu____7103 =
                                                let uu____7104 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____7104.FStar_Syntax_Syntax.n in
                                              (match uu____7103 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7121 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____7145 ->
                                                   let uu____7146 =
                                                     check_n env arg in
                                                   (match uu____7146 with
                                                    | (uu____7167,s_arg,u_arg)
                                                        ->
                                                        let uu____7170 =
                                                          let uu____7177 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7177
                                                          then
                                                            let uu____7184 =
                                                              let uu____7189
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7189, q) in
                                                            [uu____7184;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7170))))
                                     binders2 args in
                                 FStar_List.split uu____7011 in
                               (match uu____6992 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7278 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7287 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7278, uu____7287)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7353) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7359) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7365,uu____7366) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7408 = let uu____7409 = env.tc_const c in N uu____7409 in
          (uu____7408, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7410 ->
          let uu____7423 =
            let uu____7424 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7424 in
          failwith uu____7423
      | FStar_Syntax_Syntax.Tm_type uu____7431 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7438 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7457 ->
          let uu____7464 =
            let uu____7465 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7465 in
          failwith uu____7464
      | FStar_Syntax_Syntax.Tm_uvar uu____7472 ->
          let uu____7489 =
            let uu____7490 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7490 in
          failwith uu____7489
      | FStar_Syntax_Syntax.Tm_delayed uu____7497 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7528 =
            let uu____7529 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7529 in
          failwith uu____7528
and mk_match:
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
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos in
          let uu____7574 = check_n env e0 in
          match uu____7574 with
          | (uu____7587,s_e0,u_e0) ->
              let uu____7590 =
                let uu____7619 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7680 = FStar_Syntax_Subst.open_branch b in
                       match uu____7680 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___314_7722 = env in
                             let uu____7723 =
                               let uu____7724 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7724 in
                             {
                               env = uu____7723;
                               subst = (uu___314_7722.subst);
                               tc_const = (uu___314_7722.tc_const)
                             } in
                           let uu____7727 = f env1 body in
                           (match uu____7727 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7799 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____7619 in
              (match uu____7590 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7901 = FStar_List.hd nms in
                     match uu____7901 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___297_7907  ->
                          match uu___297_7907 with
                          | M uu____7908 -> true
                          | uu____7909 -> false) nms in
                   let uu____7910 =
                     let uu____7947 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8037  ->
                              match uu____8037 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8214 =
                                         check env original_body (M t2) in
                                       (match uu____8214 with
                                        | (uu____8251,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8290,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____7947 in
                   (match uu____7910 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8474  ->
                                 match uu____8474 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8525 =
                                         let uu____8526 =
                                           let uu____8541 =
                                             let uu____8548 =
                                               let uu____8553 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____8554 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____8553, uu____8554) in
                                             [uu____8548] in
                                           (s_body, uu____8541) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8526 in
                                       mk1 uu____8525 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____8586 =
                              let uu____8587 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8587] in
                            let uu____8588 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____8586 uu____8588
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____8594 =
                              let uu____8601 =
                                let uu____8602 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8602 in
                              [uu____8601] in
                            let uu____8603 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____8594 uu____8603 in
                          let uu____8606 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____8645 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____8606, uu____8645)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____8662 =
                             let uu____8665 =
                               let uu____8666 =
                                 let uu____8693 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____8693,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8666 in
                             mk1 uu____8665 in
                           let uu____8730 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____8662, uu____8730))))
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
              let uu____8777 = FStar_Syntax_Syntax.mk_binder x in
              [uu____8777] in
            let uu____8778 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____8778 with
            | (x_binders1,e21) ->
                let uu____8791 = infer env e1 in
                (match uu____8791 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____8808 = is_C t1 in
                       if uu____8808
                       then
                         let uu___315_8809 = binding in
                         let uu____8810 =
                           let uu____8813 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____8813 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___315_8809.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___315_8809.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____8810;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___315_8809.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___315_8809.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___316_8816 = env in
                       let uu____8817 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___317_8819 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___317_8819.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___317_8819.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8817;
                         subst = (uu___316_8816.subst);
                         tc_const = (uu___316_8816.tc_const)
                       } in
                     let uu____8820 = proceed env1 e21 in
                     (match uu____8820 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___318_8837 = binding in
                            let uu____8838 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___318_8837.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___318_8837.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____8838;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___318_8837.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___318_8837.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____8841 =
                            let uu____8844 =
                              let uu____8845 =
                                let uu____8858 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___319_8868 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___319_8868.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___319_8868.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___319_8868.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___319_8868.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____8858) in
                              FStar_Syntax_Syntax.Tm_let uu____8845 in
                            mk1 uu____8844 in
                          let uu____8869 =
                            let uu____8872 =
                              let uu____8873 =
                                let uu____8886 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___320_8896 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___320_8896.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___320_8896.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___320_8896.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___320_8896.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8886) in
                              FStar_Syntax_Syntax.Tm_let uu____8873 in
                            mk1 uu____8872 in
                          (nm_rec, uu____8841, uu____8869))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___321_8905 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___321_8905.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___321_8905.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___321_8905.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___322_8907 = env in
                       let uu____8908 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___323_8910 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___323_8910.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___323_8910.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8908;
                         subst = (uu___322_8907.subst);
                         tc_const = (uu___322_8907.tc_const)
                       } in
                     let uu____8911 = ensure_m env1 e21 in
                     (match uu____8911 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____8934 =
                              let uu____8935 =
                                let uu____8950 =
                                  let uu____8957 =
                                    let uu____8962 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____8963 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8962, uu____8963) in
                                  [uu____8957] in
                                (s_e2, uu____8950) in
                              FStar_Syntax_Syntax.Tm_app uu____8935 in
                            mk1 uu____8934 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____8982 =
                              let uu____8983 =
                                let uu____8998 =
                                  let uu____9005 =
                                    let uu____9010 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____9010) in
                                  [uu____9005] in
                                (s_e1, uu____8998) in
                              FStar_Syntax_Syntax.Tm_app uu____8983 in
                            mk1 uu____8982 in
                          let uu____9025 =
                            let uu____9026 =
                              let uu____9027 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9027] in
                            FStar_Syntax_Util.abs uu____9026 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____9028 =
                            let uu____9031 =
                              let uu____9032 =
                                let uu____9045 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___324_9055 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___324_9055.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___324_9055.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___324_9055.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___324_9055.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9045) in
                              FStar_Syntax_Syntax.Tm_let uu____9032 in
                            mk1 uu____9031 in
                          ((M t2), uu____9025, uu____9028)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9067 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____9067 in
      let uu____9068 = check env e mn in
      match uu____9068 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9084 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9106 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____9106 in
      let uu____9107 = check env e mn in
      match uu____9107 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9123 -> failwith "[check_m]: impossible"
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
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun t  -> FStar_Syntax_Util.comp_result t
and trans_F_:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____9153 =
           let uu____9154 = is_C c in Prims.op_Negation uu____9154 in
         if uu____9153 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____9162 =
           let uu____9163 = FStar_Syntax_Subst.compress c in
           uu____9163.FStar_Syntax_Syntax.n in
         match uu____9162 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9188 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9188 with
              | (wp_head,wp_args) ->
                  ((let uu____9226 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9240 =
                           let uu____9241 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9241 in
                         Prims.op_Negation uu____9240) in
                    if uu____9226 then failwith "mismatch" else ());
                   (let uu____9249 =
                      let uu____9250 =
                        let uu____9265 =
                          FStar_List.map2
                            (fun uu____9293  ->
                               fun uu____9294  ->
                                 match (uu____9293, uu____9294) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9331 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9331
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9334 =
                                           let uu____9339 =
                                             let uu____9340 =
                                               print_implicit q in
                                             let uu____9341 =
                                               print_implicit q' in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %b %b\n"
                                               uu____9340 uu____9341 in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9339) in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9334)
                                      else ();
                                      (let uu____9343 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9343, q)))) args wp_args in
                        (head1, uu____9265) in
                      FStar_Syntax_Syntax.Tm_app uu____9250 in
                    mk1 uu____9249)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9377 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9377 with
              | (binders_orig,comp1) ->
                  let uu____9384 =
                    let uu____9399 =
                      FStar_List.map
                        (fun uu____9433  ->
                           match uu____9433 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9453 = is_C h in
                               if uu____9453
                               then
                                 let w' =
                                   let uu____9465 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9465 in
                                 let uu____9466 =
                                   let uu____9473 =
                                     let uu____9480 =
                                       let uu____9485 =
                                         let uu____9486 =
                                           let uu____9487 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____9487 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9486 in
                                       (uu____9485, q) in
                                     [uu____9480] in
                                   (w', q) :: uu____9473 in
                                 (w', uu____9466)
                               else
                                 (let x =
                                    let uu____9508 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9508 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9399 in
                  (match uu____9384 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____9563 =
                           let uu____9566 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9566 in
                         FStar_Syntax_Subst.subst_comp uu____9563 comp1 in
                       let app =
                         let uu____9570 =
                           let uu____9571 =
                             let uu____9586 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9601 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____9602 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9601, uu____9602)) bvs in
                             (wp, uu____9586) in
                           FStar_Syntax_Syntax.Tm_app uu____9571 in
                         mk1 uu____9570 in
                       let comp3 =
                         let uu____9610 = type_of_comp comp2 in
                         let uu____9611 = is_monadic_comp comp2 in
                         trans_G env uu____9610 uu____9611 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9613,uu____9614) ->
             trans_F_ env e wp
         | uu____9655 -> failwith "impossible trans_F_")
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
            let uu____9660 =
              let uu____9661 = star_type' env h in
              let uu____9664 =
                let uu____9673 =
                  let uu____9678 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____9678) in
                [uu____9673] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9661;
                FStar_Syntax_Syntax.effect_args = uu____9664;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____9660
          else
            (let uu____9688 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____9688)
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
let star_type: env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun t  -> let uu____9699 = n env.env t in star_type' env uu____9699
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____9714 = n env.env t in check_n env uu____9714
let trans_F:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9724 = n env.env c in
        let uu____9725 = n env.env wp in trans_F_ env uu____9724 uu____9725