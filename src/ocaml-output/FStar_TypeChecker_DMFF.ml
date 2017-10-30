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
              let uu___133_104 = a in
              let uu____105 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___133_104.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___133_104.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____105
              } in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s in
            (let uu____113 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____113
             then
               (d "Elaborating extra WP combinators";
                (let uu____115 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____115))
             else ());
            (let rec collect_binders t =
               let uu____127 =
                 let uu____128 =
                   let uu____131 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____131 in
                 uu____128.FStar_Syntax_Syntax.n in
               match uu____127 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____162) -> t1
                     | uu____171 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____174 = collect_binders rest in
                   FStar_List.append bs uu____174
               | FStar_Syntax_Syntax.Tm_type uu____185 -> []
               | uu____190 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____208 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____208 FStar_Syntax_Util.name_binders in
             (let uu____228 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____228
              then
                let uu____229 =
                  let uu____230 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____230 in
                d uu____229
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____256 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____256 with
                | (sigelt,fv) ->
                    ((let uu____264 =
                        let uu____267 = FStar_ST.op_Bang sigelts in sigelt ::
                          uu____267 in
                      FStar_ST.op_Colon_Equals sigelts uu____264);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____425  ->
                     match uu____425 with
                     | (t,b) ->
                         let uu____436 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____436)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____467 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____467)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____490 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____490) in
              let uu____491 =
                let uu____506 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____528 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____528 in
                    let uu____531 =
                      let uu____532 =
                        let uu____539 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____540 =
                          let uu____543 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____543] in
                        uu____539 :: uu____540 in
                      FStar_List.append binders uu____532 in
                    FStar_Syntax_Util.abs uu____531 body
                      FStar_Pervasives_Native.None in
                  let uu____548 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____549 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____548, uu____549) in
                match uu____506 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____583 =
                        let uu____584 =
                          let uu____599 =
                            let uu____606 =
                              FStar_List.map
                                (fun uu____626  ->
                                   match uu____626 with
                                   | (bv,uu____636) ->
                                       let uu____637 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____638 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____637, uu____638)) binders in
                            let uu____639 =
                              let uu____646 =
                                let uu____651 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____652 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____651, uu____652) in
                              let uu____653 =
                                let uu____660 =
                                  let uu____665 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____665) in
                                [uu____660] in
                              uu____646 :: uu____653 in
                            FStar_List.append uu____606 uu____639 in
                          (fv, uu____599) in
                        FStar_Syntax_Syntax.Tm_app uu____584 in
                      mk1 uu____583 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____491 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____724 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____724 in
                    let ret1 =
                      let uu____728 =
                        let uu____729 =
                          let uu____732 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____732 in
                        FStar_Syntax_Util.residual_tot uu____729 in
                      FStar_Pervasives_Native.Some uu____728 in
                    let body =
                      let uu____734 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____734 ret1 in
                    let uu____735 =
                      let uu____736 = mk_all_implicit binders in
                      let uu____743 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____736 uu____743 in
                    FStar_Syntax_Util.abs uu____735 body ret1 in
                  let c_pure1 =
                    let uu____771 = mk_lid "pure" in
                    register env1 uu____771 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____776 =
                        let uu____777 =
                          let uu____778 =
                            let uu____785 =
                              let uu____786 =
                                let uu____787 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____787 in
                              FStar_Syntax_Syntax.mk_binder uu____786 in
                            [uu____785] in
                          let uu____788 =
                            let uu____791 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____791 in
                          FStar_Syntax_Util.arrow uu____778 uu____788 in
                        mk_gctx uu____777 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____776 in
                    let r =
                      let uu____793 =
                        let uu____794 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____794 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____793 in
                    let ret1 =
                      let uu____798 =
                        let uu____799 =
                          let uu____802 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____802 in
                        FStar_Syntax_Util.residual_tot uu____799 in
                      FStar_Pervasives_Native.Some uu____798 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____810 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____813 =
                          let uu____822 =
                            let uu____825 =
                              let uu____826 =
                                let uu____827 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____827
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____826 in
                            [uu____825] in
                          FStar_List.append gamma_as_args uu____822 in
                        FStar_Syntax_Util.mk_app uu____810 uu____813 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____830 =
                      let uu____831 = mk_all_implicit binders in
                      let uu____838 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____831 uu____838 in
                    FStar_Syntax_Util.abs uu____830 outer_body ret1 in
                  let c_app1 =
                    let uu____874 = mk_lid "app" in
                    register env1 uu____874 c_app in
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
                        let uu____893 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____893 in
                      FStar_Syntax_Util.arrow uu____881 uu____890 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____896 =
                        let uu____897 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____897 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____896 in
                    let ret1 =
                      let uu____901 =
                        let uu____902 =
                          let uu____905 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____905 in
                        FStar_Syntax_Util.residual_tot uu____902 in
                      FStar_Pervasives_Native.Some uu____901 in
                    let uu____906 =
                      let uu____907 = mk_all_implicit binders in
                      let uu____914 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____907 uu____914 in
                    let uu____949 =
                      let uu____950 =
                        let uu____959 =
                          let uu____962 =
                            let uu____965 =
                              let uu____974 =
                                let uu____977 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____977] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____974 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____965 in
                          let uu____978 =
                            let uu____983 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____983] in
                          uu____962 :: uu____978 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____959 in
                      FStar_Syntax_Util.mk_app c_app1 uu____950 in
                    FStar_Syntax_Util.abs uu____906 uu____949 ret1 in
                  let c_lift11 =
                    let uu____987 = mk_lid "lift1" in
                    register env1 uu____987 c_lift1 in
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
                      let uu____995 =
                        let uu____1002 =
                          let uu____1003 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1003 in
                        let uu____1004 =
                          let uu____1007 =
                            let uu____1008 =
                              FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____1008 in
                          [uu____1007] in
                        uu____1002 :: uu____1004 in
                      let uu____1009 =
                        let uu____1012 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1012 in
                      FStar_Syntax_Util.arrow uu____995 uu____1009 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1015 =
                        let uu____1016 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1016 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1015 in
                    let a2 =
                      let uu____1018 =
                        let uu____1019 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____1019 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1018 in
                    let ret1 =
                      let uu____1023 =
                        let uu____1024 =
                          let uu____1027 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____1027 in
                        FStar_Syntax_Util.residual_tot uu____1024 in
                      FStar_Pervasives_Native.Some uu____1023 in
                    let uu____1028 =
                      let uu____1029 = mk_all_implicit binders in
                      let uu____1036 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1029 uu____1036 in
                    let uu____1079 =
                      let uu____1080 =
                        let uu____1089 =
                          let uu____1092 =
                            let uu____1095 =
                              let uu____1104 =
                                let uu____1107 =
                                  let uu____1110 =
                                    let uu____1119 =
                                      let uu____1122 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1122] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1119 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1110 in
                                let uu____1123 =
                                  let uu____1128 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1128] in
                                uu____1107 :: uu____1123 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1104 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1095 in
                          let uu____1131 =
                            let uu____1136 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1136] in
                          uu____1092 :: uu____1131 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1089 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1080 in
                    FStar_Syntax_Util.abs uu____1028 uu____1079 ret1 in
                  let c_lift21 =
                    let uu____1140 = mk_lid "lift2" in
                    register env1 uu____1140 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1147 =
                        let uu____1154 =
                          let uu____1155 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1155 in
                        [uu____1154] in
                      let uu____1156 =
                        let uu____1159 =
                          let uu____1160 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1160 in
                        FStar_Syntax_Syntax.mk_Total uu____1159 in
                      FStar_Syntax_Util.arrow uu____1147 uu____1156 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1165 =
                        let uu____1166 =
                          let uu____1169 =
                            let uu____1170 =
                              let uu____1177 =
                                let uu____1178 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1178 in
                              [uu____1177] in
                            let uu____1179 =
                              let uu____1182 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1182 in
                            FStar_Syntax_Util.arrow uu____1170 uu____1179 in
                          mk_ctx uu____1169 in
                        FStar_Syntax_Util.residual_tot uu____1166 in
                      FStar_Pervasives_Native.Some uu____1165 in
                    let e1 =
                      let uu____1184 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1184 in
                    let body =
                      let uu____1186 =
                        let uu____1187 =
                          let uu____1194 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1194] in
                        FStar_List.append gamma uu____1187 in
                      let uu____1199 =
                        let uu____1200 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1203 =
                          let uu____1212 =
                            let uu____1213 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1213 in
                          let uu____1214 = args_of_binders1 gamma in
                          uu____1212 :: uu____1214 in
                        FStar_Syntax_Util.mk_app uu____1200 uu____1203 in
                      FStar_Syntax_Util.abs uu____1186 uu____1199 ret1 in
                    let uu____1217 =
                      let uu____1218 = mk_all_implicit binders in
                      let uu____1225 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1218 uu____1225 in
                    FStar_Syntax_Util.abs uu____1217 body ret1 in
                  let c_push1 =
                    let uu____1257 = mk_lid "push" in
                    register env1 uu____1257 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1277 =
                        let uu____1278 =
                          let uu____1293 = args_of_binders1 binders in
                          (c, uu____1293) in
                        FStar_Syntax_Syntax.Tm_app uu____1278 in
                      mk1 uu____1277
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1303 =
                        let uu____1304 =
                          let uu____1311 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1312 =
                            let uu____1315 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1315] in
                          uu____1311 :: uu____1312 in
                        let uu____1316 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1304 uu____1316 in
                      FStar_Syntax_Syntax.mk_Total uu____1303 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1320 =
                      let uu____1321 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1321 in
                    let uu____1332 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1334 =
                        let uu____1337 =
                          let uu____1346 =
                            let uu____1349 =
                              let uu____1352 =
                                let uu____1361 =
                                  let uu____1362 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1362 in
                                [uu____1361] in
                              FStar_Syntax_Util.mk_app l_ite uu____1352 in
                            [uu____1349] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1346 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1337 in
                      FStar_Syntax_Util.ascribe uu____1334
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1320 uu____1332
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1382 = mk_lid "wp_if_then_else" in
                    register env1 uu____1382 wp_if_then_else in
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
                      let uu____1393 =
                        let uu____1402 =
                          let uu____1405 =
                            let uu____1408 =
                              let uu____1417 =
                                let uu____1420 =
                                  let uu____1423 =
                                    let uu____1432 =
                                      let uu____1433 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1433 in
                                    [uu____1432] in
                                  FStar_Syntax_Util.mk_app l_and uu____1423 in
                                [uu____1420] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1417 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1408 in
                          let uu____1438 =
                            let uu____1443 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1443] in
                          uu____1405 :: uu____1438 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1402 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1393 in
                    let uu____1446 =
                      let uu____1447 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1447 in
                    FStar_Syntax_Util.abs uu____1446 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1459 = mk_lid "wp_assert" in
                    register env1 uu____1459 wp_assert in
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
                      let uu____1470 =
                        let uu____1479 =
                          let uu____1482 =
                            let uu____1485 =
                              let uu____1494 =
                                let uu____1497 =
                                  let uu____1500 =
                                    let uu____1509 =
                                      let uu____1510 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1510 in
                                    [uu____1509] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1500 in
                                [uu____1497] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1494 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1485 in
                          let uu____1515 =
                            let uu____1520 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1520] in
                          uu____1482 :: uu____1515 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1479 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1470 in
                    let uu____1523 =
                      let uu____1524 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1524 in
                    FStar_Syntax_Util.abs uu____1523 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1536 = mk_lid "wp_assume" in
                    register env1 uu____1536 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1545 =
                        let uu____1552 =
                          let uu____1553 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1553 in
                        [uu____1552] in
                      let uu____1554 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1545 uu____1554 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1561 =
                        let uu____1570 =
                          let uu____1573 =
                            let uu____1576 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1576 in
                          let uu____1585 =
                            let uu____1590 =
                              let uu____1593 =
                                let uu____1602 =
                                  let uu____1605 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1605] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1602 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1593 in
                            [uu____1590] in
                          uu____1573 :: uu____1585 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1570 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1561 in
                    let uu____1612 =
                      let uu____1613 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1613 in
                    FStar_Syntax_Util.abs uu____1612 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1625 = mk_lid "wp_close" in
                    register env1 uu____1625 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1635 =
                      let uu____1636 =
                        let uu____1637 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1637 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1636 in
                    FStar_Pervasives_Native.Some uu____1635 in
                  let mk_forall1 x body =
                    let uu____1649 =
                      let uu____1652 =
                        let uu____1653 =
                          let uu____1668 =
                            let uu____1671 =
                              let uu____1672 =
                                let uu____1673 =
                                  let uu____1674 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1674] in
                                FStar_Syntax_Util.abs uu____1673 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1672 in
                            [uu____1671] in
                          (FStar_Syntax_Util.tforall, uu____1668) in
                        FStar_Syntax_Syntax.Tm_app uu____1653 in
                      FStar_Syntax_Syntax.mk uu____1652 in
                    uu____1649 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1684 =
                      let uu____1685 = FStar_Syntax_Subst.compress t in
                      uu____1685.FStar_Syntax_Syntax.n in
                    match uu____1684 with
                    | FStar_Syntax_Syntax.Tm_type uu____1688 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1714  ->
                              match uu____1714 with
                              | (b,uu____1720) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1721 -> true in
                  let rec is_monotonic t =
                    let uu____1726 =
                      let uu____1727 = FStar_Syntax_Subst.compress t in
                      uu____1727.FStar_Syntax_Syntax.n in
                    match uu____1726 with
                    | FStar_Syntax_Syntax.Tm_type uu____1730 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1756  ->
                              match uu____1756 with
                              | (b,uu____1762) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1763 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1815 =
                      let uu____1816 = FStar_Syntax_Subst.compress t1 in
                      uu____1816.FStar_Syntax_Syntax.n in
                    match uu____1815 with
                    | FStar_Syntax_Syntax.Tm_type uu____1819 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1822);
                                      FStar_Syntax_Syntax.pos = uu____1823;
                                      FStar_Syntax_Syntax.vars = uu____1824;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1858 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1858
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1861 =
                              let uu____1864 =
                                let uu____1873 =
                                  let uu____1874 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1874 in
                                [uu____1873] in
                              FStar_Syntax_Util.mk_app x uu____1864 in
                            let uu____1875 =
                              let uu____1878 =
                                let uu____1887 =
                                  let uu____1888 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1888 in
                                [uu____1887] in
                              FStar_Syntax_Util.mk_app y uu____1878 in
                            mk_rel1 b uu____1861 uu____1875 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1893 =
                               let uu____1894 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1897 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1894 uu____1897 in
                             let uu____1900 =
                               let uu____1901 =
                                 let uu____1904 =
                                   let uu____1913 =
                                     let uu____1914 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1914 in
                                   [uu____1913] in
                                 FStar_Syntax_Util.mk_app x uu____1904 in
                               let uu____1915 =
                                 let uu____1918 =
                                   let uu____1927 =
                                     let uu____1928 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1928 in
                                   [uu____1927] in
                                 FStar_Syntax_Util.mk_app y uu____1918 in
                               mk_rel1 b uu____1901 uu____1915 in
                             FStar_Syntax_Util.mk_imp uu____1893 uu____1900 in
                           let uu____1929 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1929)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1932);
                                      FStar_Syntax_Syntax.pos = uu____1933;
                                      FStar_Syntax_Syntax.vars = uu____1934;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1968 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1968
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1971 =
                              let uu____1974 =
                                let uu____1983 =
                                  let uu____1984 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1984 in
                                [uu____1983] in
                              FStar_Syntax_Util.mk_app x uu____1974 in
                            let uu____1985 =
                              let uu____1988 =
                                let uu____1997 =
                                  let uu____1998 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1998 in
                                [uu____1997] in
                              FStar_Syntax_Util.mk_app y uu____1988 in
                            mk_rel1 b uu____1971 uu____1985 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____2003 =
                               let uu____2004 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____2007 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____2004 uu____2007 in
                             let uu____2010 =
                               let uu____2011 =
                                 let uu____2014 =
                                   let uu____2023 =
                                     let uu____2024 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2024 in
                                   [uu____2023] in
                                 FStar_Syntax_Util.mk_app x uu____2014 in
                               let uu____2025 =
                                 let uu____2028 =
                                   let uu____2037 =
                                     let uu____2038 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2038 in
                                   [uu____2037] in
                                 FStar_Syntax_Util.mk_app y uu____2028 in
                               mk_rel1 b uu____2011 uu____2025 in
                             FStar_Syntax_Util.mk_imp uu____2003 uu____2010 in
                           let uu____2039 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2039)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___134_2070 = t1 in
                          let uu____2071 =
                            let uu____2072 =
                              let uu____2085 =
                                let uu____2086 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2086 in
                              ([binder], uu____2085) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2072 in
                          {
                            FStar_Syntax_Syntax.n = uu____2071;
                            FStar_Syntax_Syntax.pos =
                              (uu___134_2070.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___134_2070.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2101 ->
                        failwith "unhandled arrow"
                    | uu____2114 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2129 =
                        let uu____2130 = FStar_Syntax_Subst.compress t1 in
                        uu____2130.FStar_Syntax_Syntax.n in
                      match uu____2129 with
                      | FStar_Syntax_Syntax.Tm_type uu____2133 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2156 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2156
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2171 =
                                let uu____2172 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2172 i in
                              FStar_Syntax_Syntax.fvar uu____2171
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2199 =
                            let uu____2206 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2220  ->
                                     match uu____2220 with
                                     | (t2,q) ->
                                         let uu____2227 = project i x in
                                         let uu____2228 = project i y in
                                         mk_stronger t2 uu____2227 uu____2228)
                                args in
                            match uu____2206 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2199 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2255);
                                      FStar_Syntax_Syntax.pos = uu____2256;
                                      FStar_Syntax_Syntax.vars = uu____2257;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2295  ->
                                   match uu____2295 with
                                   | (bv,q) ->
                                       let uu____2302 =
                                         let uu____2303 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2303 in
                                       FStar_Syntax_Syntax.gen_bv uu____2302
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2310 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2310) bvs in
                          let body =
                            let uu____2312 = FStar_Syntax_Util.mk_app x args in
                            let uu____2313 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2312 uu____2313 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2320);
                                      FStar_Syntax_Syntax.pos = uu____2321;
                                      FStar_Syntax_Syntax.vars = uu____2322;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2360  ->
                                   match uu____2360 with
                                   | (bv,q) ->
                                       let uu____2367 =
                                         let uu____2368 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2368 in
                                       FStar_Syntax_Syntax.gen_bv uu____2367
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2375 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2375) bvs in
                          let body =
                            let uu____2377 = FStar_Syntax_Util.mk_app x args in
                            let uu____2378 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2377 uu____2378 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2383 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2385 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2386 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2387 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2385 uu____2386 uu____2387 in
                    let uu____2388 =
                      let uu____2389 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2389 in
                    FStar_Syntax_Util.abs uu____2388 body ret_tot_type in
                  let stronger1 =
                    let uu____2417 = mk_lid "stronger" in
                    register env1 uu____2417 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2423 = FStar_Util.prefix gamma in
                    match uu____2423 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2468 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2468 in
                          let uu____2471 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2471 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2481 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2481 in
                              let guard_free1 =
                                let uu____2491 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2491 in
                              let pat =
                                let uu____2495 =
                                  let uu____2504 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2504] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2495 in
                              let pattern_guarded_body =
                                let uu____2508 =
                                  let uu____2509 =
                                    let uu____2516 =
                                      let uu____2517 =
                                        let uu____2528 =
                                          let uu____2531 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2531] in
                                        [uu____2528] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2517 in
                                    (body, uu____2516) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2509 in
                                mk1 uu____2508 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2536 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2540 =
                            let uu____2541 =
                              let uu____2542 =
                                let uu____2543 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2546 =
                                  let uu____2555 = args_of_binders1 wp_args in
                                  let uu____2558 =
                                    let uu____2561 =
                                      let uu____2562 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2562 in
                                    [uu____2561] in
                                  FStar_List.append uu____2555 uu____2558 in
                                FStar_Syntax_Util.mk_app uu____2543
                                  uu____2546 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2542 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2541 in
                          FStar_Syntax_Util.abs gamma uu____2540
                            ret_gtot_type in
                        let uu____2563 =
                          let uu____2564 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2564 in
                        FStar_Syntax_Util.abs uu____2563 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2576 = mk_lid "wp_ite" in
                    register env1 uu____2576 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2582 = FStar_Util.prefix gamma in
                    match uu____2582 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2625 =
                            let uu____2626 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2629 =
                              let uu____2638 =
                                let uu____2639 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2639 in
                              [uu____2638] in
                            FStar_Syntax_Util.mk_app uu____2626 uu____2629 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2625 in
                        let uu____2640 =
                          let uu____2641 =
                            let uu____2648 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2648 gamma in
                          FStar_List.append binders uu____2641 in
                        FStar_Syntax_Util.abs uu____2640 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2664 = mk_lid "null_wp" in
                    register env1 uu____2664 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2673 =
                        let uu____2682 =
                          let uu____2685 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2686 =
                            let uu____2689 =
                              let uu____2692 =
                                let uu____2701 =
                                  let uu____2702 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2702 in
                                [uu____2701] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2692 in
                            let uu____2703 =
                              let uu____2708 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2708] in
                            uu____2689 :: uu____2703 in
                          uu____2685 :: uu____2686 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2682 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2673 in
                    let uu____2711 =
                      let uu____2712 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2712 in
                    FStar_Syntax_Util.abs uu____2711 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2724 = mk_lid "wp_trivial" in
                    register env1 uu____2724 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2729 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2729
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2734 =
                      let uu____2737 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____2737 in
                    let uu____2804 =
                      let uu___135_2805 = ed in
                      let uu____2806 =
                        let uu____2807 = c wp_if_then_else2 in
                        ([], uu____2807) in
                      let uu____2810 =
                        let uu____2811 = c wp_ite2 in ([], uu____2811) in
                      let uu____2814 =
                        let uu____2815 = c stronger2 in ([], uu____2815) in
                      let uu____2818 =
                        let uu____2819 = c wp_close2 in ([], uu____2819) in
                      let uu____2822 =
                        let uu____2823 = c wp_assert2 in ([], uu____2823) in
                      let uu____2826 =
                        let uu____2827 = c wp_assume2 in ([], uu____2827) in
                      let uu____2830 =
                        let uu____2831 = c null_wp2 in ([], uu____2831) in
                      let uu____2834 =
                        let uu____2835 = c wp_trivial2 in ([], uu____2835) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___135_2805.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___135_2805.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___135_2805.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___135_2805.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___135_2805.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___135_2805.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___135_2805.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2806;
                        FStar_Syntax_Syntax.ite_wp = uu____2810;
                        FStar_Syntax_Syntax.stronger = uu____2814;
                        FStar_Syntax_Syntax.close_wp = uu____2818;
                        FStar_Syntax_Syntax.assert_p = uu____2822;
                        FStar_Syntax_Syntax.assume_p = uu____2826;
                        FStar_Syntax_Syntax.null_wp = uu____2830;
                        FStar_Syntax_Syntax.trivial = uu____2834;
                        FStar_Syntax_Syntax.repr =
                          (uu___135_2805.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___135_2805.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___135_2805.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___135_2805.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2734, uu____2804)))))
type env_ = env[@@deriving show]
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___136_2852 = dmff_env in
      {
        env = env';
        subst = (uu___136_2852.subst);
        tc_const = (uu___136_2852.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ[@@deriving show]
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2866 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2880 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm[@@deriving show]
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___122_2892  ->
    match uu___122_2892 with
    | FStar_Syntax_Syntax.Total (t,uu____2894) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___121_2907  ->
                match uu___121_2907 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2908 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2910 =
          let uu____2911 =
            let uu____2912 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2912 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2911 in
        failwith uu____2910
    | FStar_Syntax_Syntax.GTotal uu____2913 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___123_2925  ->
    match uu___123_2925 with
    | N t ->
        let uu____2927 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2927
    | M t ->
        let uu____2929 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2929
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2934,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2936;
                      FStar_Syntax_Syntax.vars = uu____2937;_})
        -> nm_of_comp n2
    | uu____2954 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____2963 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____2963 with | M uu____2964 -> true | N uu____2965 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2970 -> false
let double_star: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ  ->
    let star_once typ1 =
      let uu____2981 =
        let uu____2988 =
          let uu____2989 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2989 in
        [uu____2988] in
      let uu____2990 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2981 uu____2990 in
    let uu____2993 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2993
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
          (let uu____3030 =
             let uu____3043 =
               let uu____3050 =
                 let uu____3055 =
                   let uu____3056 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____3056 in
                 let uu____3057 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____3055, uu____3057) in
               [uu____3050] in
             let uu____3066 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____3043, uu____3066) in
           FStar_Syntax_Syntax.Tm_arrow uu____3030)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3094) ->
          let binders1 =
            FStar_List.map
              (fun uu____3130  ->
                 match uu____3130 with
                 | (bv,aqual) ->
                     let uu____3141 =
                       let uu___137_3142 = bv in
                       let uu____3143 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___137_3142.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___137_3142.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3143
                       } in
                     (uu____3141, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3146,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3148);
                             FStar_Syntax_Syntax.pos = uu____3149;
                             FStar_Syntax_Syntax.vars = uu____3150;_})
               ->
               let uu____3175 =
                 let uu____3176 =
                   let uu____3189 =
                     let uu____3190 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3190 in
                   (binders1, uu____3189) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3176 in
               mk1 uu____3175
           | uu____3197 ->
               let uu____3198 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3198 with
                | N hn ->
                    let uu____3200 =
                      let uu____3201 =
                        let uu____3214 =
                          let uu____3215 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3215 in
                        (binders1, uu____3214) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3201 in
                    mk1 uu____3200
                | M a ->
                    let uu____3223 =
                      let uu____3224 =
                        let uu____3237 =
                          let uu____3244 =
                            let uu____3251 =
                              let uu____3256 =
                                let uu____3257 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3257 in
                              let uu____3258 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3256, uu____3258) in
                            [uu____3251] in
                          FStar_List.append binders1 uu____3244 in
                        let uu____3271 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3237, uu____3271) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3224 in
                    mk1 uu____3223))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3337 = f x in
                    FStar_Util.string_builder_append strb uu____3337);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3344 = f x1 in
                         FStar_Util.string_builder_append strb uu____3344))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3346 = FStar_Syntax_Print.term_to_string t2 in
            let uu____3347 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____3346 uu____3347 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3355 =
              let uu____3356 = FStar_Syntax_Subst.compress ty in
              uu____3356.FStar_Syntax_Syntax.n in
            match uu____3355 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3377 =
                  let uu____3378 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3378 in
                if uu____3377
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3404 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3404 s in
                       let uu____3407 =
                         let uu____3408 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3408 in
                       if uu____3407
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else () in
                     let uu____3411 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3411 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3433  ->
                                  match uu____3433 with
                                  | (bv,uu____3443) ->
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
            | uu____3457 ->
                ((let uu____3459 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____3459);
                 false) in
          let rec is_valid_application head2 =
            let uu____3464 =
              let uu____3465 = FStar_Syntax_Subst.compress head2 in
              uu____3465.FStar_Syntax_Syntax.n in
            match uu____3464 with
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
                  (let uu____3470 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3470)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3472 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3472 with
                 | ((uu____3481,ty),uu____3483) ->
                     let uu____3488 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3488
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3496 -> true
                        | uu____3511 ->
                            ((let uu____3513 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____3513);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3515 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3516 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3518) ->
                is_valid_application t2
            | uu____3523 -> false in
          let uu____3524 = is_valid_application head1 in
          if uu____3524
          then
            let uu____3525 =
              let uu____3526 =
                let uu____3541 =
                  FStar_List.map
                    (fun uu____3562  ->
                       match uu____3562 with
                       | (t2,qual) ->
                           let uu____3579 = star_type' env t2 in
                           (uu____3579, qual)) args in
                (head1, uu____3541) in
              FStar_Syntax_Syntax.Tm_app uu____3526 in
            mk1 uu____3525
          else
            (let uu____3589 =
               let uu____3590 =
                 let uu____3591 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3591 in
               FStar_Errors.Err uu____3590 in
             FStar_Exn.raise uu____3589)
      | FStar_Syntax_Syntax.Tm_bvar uu____3592 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3593 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3594 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3595 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3619 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3619 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___140_3627 = env in
                 let uu____3628 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3628;
                   subst = (uu___140_3627.subst);
                   tc_const = (uu___140_3627.tc_const)
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
               ((let uu___141_3648 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___141_3648.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___141_3648.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3655 =
            let uu____3656 =
              let uu____3663 = star_type' env t2 in (uu____3663, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3656 in
          mk1 uu____3655
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3711 =
            let uu____3712 =
              let uu____3739 = star_type' env e in
              let uu____3740 =
                let uu____3755 =
                  let uu____3762 = star_type' env t2 in
                  FStar_Util.Inl uu____3762 in
                (uu____3755, FStar_Pervasives_Native.None) in
              (uu____3739, uu____3740, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3712 in
          mk1 uu____3711
      | FStar_Syntax_Syntax.Tm_ascribed uu____3793 ->
          let uu____3820 =
            let uu____3821 =
              let uu____3822 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____3822 in
            FStar_Errors.Err uu____3821 in
          FStar_Exn.raise uu____3820
      | FStar_Syntax_Syntax.Tm_refine uu____3823 ->
          let uu____3830 =
            let uu____3831 =
              let uu____3832 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3832 in
            FStar_Errors.Err uu____3831 in
          FStar_Exn.raise uu____3830
      | FStar_Syntax_Syntax.Tm_uinst uu____3833 ->
          let uu____3840 =
            let uu____3841 =
              let uu____3842 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3842 in
            FStar_Errors.Err uu____3841 in
          FStar_Exn.raise uu____3840
      | FStar_Syntax_Syntax.Tm_constant uu____3843 ->
          let uu____3844 =
            let uu____3845 =
              let uu____3846 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3846 in
            FStar_Errors.Err uu____3845 in
          FStar_Exn.raise uu____3844
      | FStar_Syntax_Syntax.Tm_match uu____3847 ->
          let uu____3870 =
            let uu____3871 =
              let uu____3872 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3872 in
            FStar_Errors.Err uu____3871 in
          FStar_Exn.raise uu____3870
      | FStar_Syntax_Syntax.Tm_let uu____3873 ->
          let uu____3886 =
            let uu____3887 =
              let uu____3888 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____3888 in
            FStar_Errors.Err uu____3887 in
          FStar_Exn.raise uu____3886
      | FStar_Syntax_Syntax.Tm_uvar uu____3889 ->
          let uu____3906 =
            let uu____3907 =
              let uu____3908 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____3908 in
            FStar_Errors.Err uu____3907 in
          FStar_Exn.raise uu____3906
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____3909 =
            let uu____3910 =
              let uu____3911 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____3911 in
            FStar_Errors.Err uu____3910 in
          FStar_Exn.raise uu____3909
      | FStar_Syntax_Syntax.Tm_delayed uu____3912 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___125_3942  ->
    match uu___125_3942 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___124_3949  ->
                match uu___124_3949 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3950 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3955 =
      let uu____3956 = FStar_Syntax_Subst.compress t in
      uu____3956.FStar_Syntax_Syntax.n in
    match uu____3955 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3982 =
            let uu____3983 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____3983 in
          is_C uu____3982 in
        if r
        then
          ((let uu____3999 =
              let uu____4000 =
                FStar_List.for_all
                  (fun uu____4008  ->
                     match uu____4008 with | (h,uu____4014) -> is_C h) args in
              Prims.op_Negation uu____4000 in
            if uu____3999 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4018 =
              let uu____4019 =
                FStar_List.for_all
                  (fun uu____4028  ->
                     match uu____4028 with
                     | (h,uu____4034) ->
                         let uu____4035 = is_C h in
                         Prims.op_Negation uu____4035) args in
              Prims.op_Negation uu____4019 in
            if uu____4018 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4055 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4055 with
         | M t1 ->
             ((let uu____4058 = is_C t1 in
               if uu____4058 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4062) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4068) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4074,uu____4075) -> is_C t1
    | uu____4116 -> false
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
          let uu____4142 =
            let uu____4143 =
              let uu____4158 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4159 =
                let uu____4166 =
                  let uu____4171 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4171) in
                [uu____4166] in
              (uu____4158, uu____4159) in
            FStar_Syntax_Syntax.Tm_app uu____4143 in
          mk1 uu____4142 in
        let uu____4186 =
          let uu____4187 = FStar_Syntax_Syntax.mk_binder p in [uu____4187] in
        FStar_Syntax_Util.abs uu____4186 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___126_4191  ->
    match uu___126_4191 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4192 -> false
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
        let return_if uu____4367 =
          match uu____4367 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4394 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4396 =
                       let uu____4397 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4397 in
                     Prims.op_Negation uu____4396) in
                if uu____4394
                then
                  let uu____4398 =
                    let uu____4399 =
                      let uu____4400 = FStar_Syntax_Print.term_to_string e in
                      let uu____4401 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4402 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4400 uu____4401 uu____4402 in
                    FStar_Errors.Err uu____4399 in
                  FStar_Exn.raise uu____4398
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4419 = mk_return env t1 s_e in
                     ((M t1), uu____4419, u_e)))
               | (M t1,N t2) ->
                   let uu____4422 =
                     let uu____4423 =
                       let uu____4424 = FStar_Syntax_Print.term_to_string e in
                       let uu____4425 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4426 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4424 uu____4425 uu____4426 in
                     FStar_Errors.Err uu____4423 in
                   FStar_Exn.raise uu____4422) in
        let ensure_m env1 e2 =
          let strip_m uu___127_4467 =
            match uu___127_4467 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4483 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4503 =
                let uu____4504 =
                  let uu____4509 =
                    let uu____4510 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____4510 in
                  (uu____4509, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____4504 in
              FStar_Exn.raise uu____4503
          | M uu____4517 ->
              let uu____4518 = check env1 e2 context_nm in strip_m uu____4518 in
        let uu____4525 =
          let uu____4526 = FStar_Syntax_Subst.compress e in
          uu____4526.FStar_Syntax_Syntax.n in
        match uu____4525 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4535 ->
            let uu____4536 = infer env e in return_if uu____4536
        | FStar_Syntax_Syntax.Tm_name uu____4543 ->
            let uu____4544 = infer env e in return_if uu____4544
        | FStar_Syntax_Syntax.Tm_fvar uu____4551 ->
            let uu____4552 = infer env e in return_if uu____4552
        | FStar_Syntax_Syntax.Tm_abs uu____4559 ->
            let uu____4576 = infer env e in return_if uu____4576
        | FStar_Syntax_Syntax.Tm_constant uu____4583 ->
            let uu____4584 = infer env e in return_if uu____4584
        | FStar_Syntax_Syntax.Tm_app uu____4591 ->
            let uu____4606 = infer env e in return_if uu____4606
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4674) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4680) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4686,uu____4687) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4728 ->
            let uu____4741 =
              let uu____4742 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4742 in
            failwith uu____4741
        | FStar_Syntax_Syntax.Tm_type uu____4749 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4756 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4775 ->
            let uu____4782 =
              let uu____4783 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4783 in
            failwith uu____4782
        | FStar_Syntax_Syntax.Tm_uvar uu____4790 ->
            let uu____4807 =
              let uu____4808 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4808 in
            failwith uu____4807
        | FStar_Syntax_Syntax.Tm_delayed uu____4815 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4846 =
              let uu____4847 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4847 in
            failwith uu____4846
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
      let uu____4871 =
        let uu____4872 = FStar_Syntax_Subst.compress e in
        uu____4872.FStar_Syntax_Syntax.n in
      match uu____4871 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____4931;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____4932;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____4938 =
                  let uu___142_4939 = rc in
                  let uu____4940 =
                    let uu____4945 =
                      let uu____4946 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____4946 in
                    FStar_Pervasives_Native.Some uu____4945 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___142_4939.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____4940;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___142_4939.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____4938 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___143_4956 = env in
            let uu____4957 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____4957;
              subst = (uu___143_4956.subst);
              tc_const = (uu___143_4956.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____4977  ->
                 match uu____4977 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___144_4990 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___144_4990.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___144_4990.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____4991 =
            FStar_List.fold_left
              (fun uu____5020  ->
                 fun uu____5021  ->
                   match (uu____5020, uu____5021) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5069 = is_C c in
                       if uu____5069
                       then
                         let xw =
                           let uu____5077 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5077 in
                         let x =
                           let uu___145_5079 = bv in
                           let uu____5080 =
                             let uu____5083 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5083 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___145_5079.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___145_5079.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5080
                           } in
                         let env3 =
                           let uu___146_5085 = env2 in
                           let uu____5086 =
                             let uu____5089 =
                               let uu____5090 =
                                 let uu____5097 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5097) in
                               FStar_Syntax_Syntax.NT uu____5090 in
                             uu____5089 :: (env2.subst) in
                           {
                             env = (uu___146_5085.env);
                             subst = uu____5086;
                             tc_const = (uu___146_5085.tc_const)
                           } in
                         let uu____5098 =
                           let uu____5101 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5102 =
                             let uu____5105 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5105 :: acc in
                           uu____5101 :: uu____5102 in
                         (env3, uu____5098)
                       else
                         (let x =
                            let uu___147_5110 = bv in
                            let uu____5111 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___147_5110.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___147_5110.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5111
                            } in
                          let uu____5114 =
                            let uu____5117 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5117 :: acc in
                          (env2, uu____5114))) (env1, []) binders1 in
          (match uu____4991 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5137 =
                 let check_what =
                   let uu____5155 = is_monadic rc_opt1 in
                   if uu____5155 then check_m else check_n in
                 let uu____5167 = check_what env2 body1 in
                 match uu____5167 with
                 | (t,s_body,u_body) ->
                     let uu____5183 =
                       let uu____5184 =
                         let uu____5185 = is_monadic rc_opt1 in
                         if uu____5185 then M t else N t in
                       comp_of_nm uu____5184 in
                     (uu____5183, s_body, u_body) in
               (match uu____5137 with
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
                                 let uu____5210 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___128_5214  ->
                                           match uu___128_5214 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5215 -> false)) in
                                 if uu____5210
                                 then
                                   let uu____5216 =
                                     FStar_List.filter
                                       (fun uu___129_5220  ->
                                          match uu___129_5220 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5221 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5216
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5230 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___130_5234  ->
                                         match uu___130_5234 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5235 -> false)) in
                               if uu____5230
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___131_5242  ->
                                        match uu___131_5242 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5243 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5244 =
                                   let uu____5245 =
                                     let uu____5250 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5250 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5245 flags in
                                 FStar_Pervasives_Native.Some uu____5244
                               else
                                 (let uu____5252 =
                                    let uu___148_5253 = rc in
                                    let uu____5254 =
                                      let uu____5259 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5259 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___148_5253.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5254;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___148_5253.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5252)) in
                    let uu____5260 =
                      let comp1 =
                        let uu____5270 = is_monadic rc_opt1 in
                        let uu____5271 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5270 uu____5271 in
                      let uu____5272 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5272,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5260 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5314 =
                             let uu____5315 =
                               let uu____5332 =
                                 let uu____5335 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5335 s_rc_opt in
                               (s_binders1, s_body1, uu____5332) in
                             FStar_Syntax_Syntax.Tm_abs uu____5315 in
                           mk1 uu____5314 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5345 =
                             let uu____5346 =
                               let uu____5363 =
                                 let uu____5366 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5366 u_rc_opt in
                               (u_binders2, u_body2, uu____5363) in
                             FStar_Syntax_Syntax.Tm_abs uu____5346 in
                           mk1 uu____5345 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5376;_};
            FStar_Syntax_Syntax.fv_delta = uu____5377;
            FStar_Syntax_Syntax.fv_qual = uu____5378;_}
          ->
          let uu____5381 =
            let uu____5386 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5386 in
          (match uu____5381 with
           | (uu____5417,t) ->
               let uu____5419 = let uu____5420 = normalize1 t in N uu____5420 in
               (uu____5419, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5421;
             FStar_Syntax_Syntax.vars = uu____5422;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5485 = FStar_Syntax_Util.head_and_args e in
          (match uu____5485 with
           | (unary_op,uu____5507) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5566;
             FStar_Syntax_Syntax.vars = uu____5567;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5643 = FStar_Syntax_Util.head_and_args e in
          (match uu____5643 with
           | (unary_op,uu____5665) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5730;
             FStar_Syntax_Syntax.vars = uu____5731;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____5769 = infer env a in
          (match uu____5769 with
           | (t,s,u) ->
               let uu____5785 = FStar_Syntax_Util.head_and_args e in
               (match uu____5785 with
                | (head1,uu____5807) ->
                    let uu____5828 =
                      let uu____5829 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____5829 in
                    let uu____5830 =
                      let uu____5833 =
                        let uu____5834 =
                          let uu____5849 =
                            let uu____5852 = FStar_Syntax_Syntax.as_arg s in
                            [uu____5852] in
                          (head1, uu____5849) in
                        FStar_Syntax_Syntax.Tm_app uu____5834 in
                      mk1 uu____5833 in
                    let uu____5857 =
                      let uu____5860 =
                        let uu____5861 =
                          let uu____5876 =
                            let uu____5879 = FStar_Syntax_Syntax.as_arg u in
                            [uu____5879] in
                          (head1, uu____5876) in
                        FStar_Syntax_Syntax.Tm_app uu____5861 in
                      mk1 uu____5860 in
                    (uu____5828, uu____5830, uu____5857)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5888;
             FStar_Syntax_Syntax.vars = uu____5889;_},(a1,uu____5891)::a2::[])
          ->
          let uu____5933 = infer env a1 in
          (match uu____5933 with
           | (t,s,u) ->
               let uu____5949 = FStar_Syntax_Util.head_and_args e in
               (match uu____5949 with
                | (head1,uu____5971) ->
                    let uu____5992 =
                      let uu____5995 =
                        let uu____5996 =
                          let uu____6011 =
                            let uu____6014 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6014; a2] in
                          (head1, uu____6011) in
                        FStar_Syntax_Syntax.Tm_app uu____5996 in
                      mk1 uu____5995 in
                    let uu____6031 =
                      let uu____6034 =
                        let uu____6035 =
                          let uu____6050 =
                            let uu____6053 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6053; a2] in
                          (head1, uu____6050) in
                        FStar_Syntax_Syntax.Tm_app uu____6035 in
                      mk1 uu____6034 in
                    (t, uu____5992, uu____6031)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6074;
             FStar_Syntax_Syntax.vars = uu____6075;_},uu____6076)
          ->
          let uu____6097 =
            let uu____6098 =
              let uu____6103 =
                let uu____6104 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6104 in
              (uu____6103, (e.FStar_Syntax_Syntax.pos)) in
            FStar_Errors.Error uu____6098 in
          FStar_Exn.raise uu____6097
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6111;
             FStar_Syntax_Syntax.vars = uu____6112;_},uu____6113)
          ->
          let uu____6134 =
            let uu____6135 =
              let uu____6140 =
                let uu____6141 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6141 in
              (uu____6140, (e.FStar_Syntax_Syntax.pos)) in
            FStar_Errors.Error uu____6135 in
          FStar_Exn.raise uu____6134
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6170 = check_n env head1 in
          (match uu____6170 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6190 =
                   let uu____6191 = FStar_Syntax_Subst.compress t in
                   uu____6191.FStar_Syntax_Syntax.n in
                 match uu____6190 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6194 -> true
                 | uu____6207 -> false in
               let rec flatten1 t =
                 let uu____6224 =
                   let uu____6225 = FStar_Syntax_Subst.compress t in
                   uu____6225.FStar_Syntax_Syntax.n in
                 match uu____6224 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6242);
                                FStar_Syntax_Syntax.pos = uu____6243;
                                FStar_Syntax_Syntax.vars = uu____6244;_})
                     when is_arrow t1 ->
                     let uu____6269 = flatten1 t1 in
                     (match uu____6269 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6351,uu____6352)
                     -> flatten1 e1
                 | uu____6393 ->
                     let uu____6394 =
                       let uu____6395 =
                         let uu____6396 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6396 in
                       FStar_Errors.Err uu____6395 in
                     FStar_Exn.raise uu____6394 in
               let uu____6409 = flatten1 t_head in
               (match uu____6409 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6469 =
                          let uu____6470 =
                            let uu____6471 = FStar_Util.string_of_int n1 in
                            let uu____6478 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____6489 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6471 uu____6478 uu____6489 in
                          FStar_Errors.Err uu____6470 in
                        FStar_Exn.raise uu____6469)
                     else ();
                     (let uu____6497 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____6497 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6538 args1 =
                            match uu____6538 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6612 =
                                       let uu____6613 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____6613.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____6612
                                 | (binders3,[]) ->
                                     let uu____6643 =
                                       let uu____6644 =
                                         let uu____6647 =
                                           let uu____6648 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6648 in
                                         FStar_Syntax_Subst.compress
                                           uu____6647 in
                                       uu____6644.FStar_Syntax_Syntax.n in
                                     (match uu____6643 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6673 =
                                            let uu____6674 =
                                              let uu____6675 =
                                                let uu____6688 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____6688) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6675 in
                                            mk1 uu____6674 in
                                          N uu____6673
                                      | uu____6695 -> failwith "wat?")
                                 | ([],uu____6696::uu____6697) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6737)::binders3,(arg,uu____6740)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____6793 = FStar_List.splitAt n' binders1 in
                          (match uu____6793 with
                           | (binders2,uu____6825) ->
                               let uu____6850 =
                                 let uu____6869 =
                                   FStar_List.map2
                                     (fun uu____6917  ->
                                        fun uu____6918  ->
                                          match (uu____6917, uu____6918) with
                                          | ((bv,uu____6950),(arg,q)) ->
                                              let uu____6961 =
                                                let uu____6962 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____6962.FStar_Syntax_Syntax.n in
                                              (match uu____6961 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____6979 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____7003 ->
                                                   let uu____7004 =
                                                     check_n env arg in
                                                   (match uu____7004 with
                                                    | (uu____7025,s_arg,u_arg)
                                                        ->
                                                        let uu____7028 =
                                                          let uu____7035 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7035
                                                          then
                                                            let uu____7042 =
                                                              let uu____7047
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7047, q) in
                                                            [uu____7042;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7028))))
                                     binders2 args in
                                 FStar_List.split uu____6869 in
                               (match uu____6850 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7136 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7145 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7136, uu____7145)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7211) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7217) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7223,uu____7224) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7266 = let uu____7267 = env.tc_const c in N uu____7267 in
          (uu____7266, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7268 ->
          let uu____7281 =
            let uu____7282 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7282 in
          failwith uu____7281
      | FStar_Syntax_Syntax.Tm_type uu____7289 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7296 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7315 ->
          let uu____7322 =
            let uu____7323 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7323 in
          failwith uu____7322
      | FStar_Syntax_Syntax.Tm_uvar uu____7330 ->
          let uu____7347 =
            let uu____7348 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7348 in
          failwith uu____7347
      | FStar_Syntax_Syntax.Tm_delayed uu____7355 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7386 =
            let uu____7387 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7387 in
          failwith uu____7386
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
          let uu____7432 = check_n env e0 in
          match uu____7432 with
          | (uu____7445,s_e0,u_e0) ->
              let uu____7448 =
                let uu____7477 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7538 = FStar_Syntax_Subst.open_branch b in
                       match uu____7538 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___149_7580 = env in
                             let uu____7581 =
                               let uu____7582 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7582 in
                             {
                               env = uu____7581;
                               subst = (uu___149_7580.subst);
                               tc_const = (uu___149_7580.tc_const)
                             } in
                           let uu____7585 = f env1 body in
                           (match uu____7585 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7657 ->
                           FStar_Exn.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____7477 in
              (match uu____7448 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7759 = FStar_List.hd nms in
                     match uu____7759 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___132_7765  ->
                          match uu___132_7765 with
                          | M uu____7766 -> true
                          | uu____7767 -> false) nms in
                   let uu____7768 =
                     let uu____7805 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____7895  ->
                              match uu____7895 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8072 =
                                         check env original_body (M t2) in
                                       (match uu____8072 with
                                        | (uu____8109,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8148,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____7805 in
                   (match uu____7768 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8332  ->
                                 match uu____8332 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8383 =
                                         let uu____8384 =
                                           let uu____8399 =
                                             let uu____8406 =
                                               let uu____8411 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____8412 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____8411, uu____8412) in
                                             [uu____8406] in
                                           (s_body, uu____8399) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8384 in
                                       mk1 uu____8383 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____8444 =
                              let uu____8445 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8445] in
                            let uu____8446 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____8444 uu____8446
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____8452 =
                              let uu____8459 =
                                let uu____8460 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8460 in
                              [uu____8459] in
                            let uu____8461 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____8452 uu____8461 in
                          let uu____8464 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____8503 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____8464, uu____8503)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____8520 =
                             let uu____8523 =
                               let uu____8524 =
                                 let uu____8551 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____8551,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8524 in
                             mk1 uu____8523 in
                           let uu____8588 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____8520, uu____8588))))
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
              let uu____8635 = FStar_Syntax_Syntax.mk_binder x in
              [uu____8635] in
            let uu____8636 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____8636 with
            | (x_binders1,e21) ->
                let uu____8649 = infer env e1 in
                (match uu____8649 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____8666 = is_C t1 in
                       if uu____8666
                       then
                         let uu___150_8667 = binding in
                         let uu____8668 =
                           let uu____8671 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____8671 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___150_8667.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___150_8667.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____8668;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___150_8667.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___150_8667.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___151_8674 = env in
                       let uu____8675 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___152_8677 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___152_8677.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___152_8677.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8675;
                         subst = (uu___151_8674.subst);
                         tc_const = (uu___151_8674.tc_const)
                       } in
                     let uu____8678 = proceed env1 e21 in
                     (match uu____8678 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___153_8695 = binding in
                            let uu____8696 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___153_8695.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___153_8695.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____8696;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___153_8695.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___153_8695.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____8699 =
                            let uu____8702 =
                              let uu____8703 =
                                let uu____8716 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___154_8726 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___154_8726.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___154_8726.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___154_8726.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___154_8726.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____8716) in
                              FStar_Syntax_Syntax.Tm_let uu____8703 in
                            mk1 uu____8702 in
                          let uu____8727 =
                            let uu____8730 =
                              let uu____8731 =
                                let uu____8744 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___155_8754 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___155_8754.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___155_8754.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___155_8754.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___155_8754.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8744) in
                              FStar_Syntax_Syntax.Tm_let uu____8731 in
                            mk1 uu____8730 in
                          (nm_rec, uu____8699, uu____8727))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___156_8763 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___156_8763.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___156_8763.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___156_8763.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___157_8765 = env in
                       let uu____8766 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___158_8768 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___158_8768.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___158_8768.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8766;
                         subst = (uu___157_8765.subst);
                         tc_const = (uu___157_8765.tc_const)
                       } in
                     let uu____8769 = ensure_m env1 e21 in
                     (match uu____8769 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____8792 =
                              let uu____8793 =
                                let uu____8808 =
                                  let uu____8815 =
                                    let uu____8820 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____8821 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8820, uu____8821) in
                                  [uu____8815] in
                                (s_e2, uu____8808) in
                              FStar_Syntax_Syntax.Tm_app uu____8793 in
                            mk1 uu____8792 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____8840 =
                              let uu____8841 =
                                let uu____8856 =
                                  let uu____8863 =
                                    let uu____8868 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____8868) in
                                  [uu____8863] in
                                (s_e1, uu____8856) in
                              FStar_Syntax_Syntax.Tm_app uu____8841 in
                            mk1 uu____8840 in
                          let uu____8883 =
                            let uu____8884 =
                              let uu____8885 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8885] in
                            FStar_Syntax_Util.abs uu____8884 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____8886 =
                            let uu____8889 =
                              let uu____8890 =
                                let uu____8903 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___159_8913 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___159_8913.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___159_8913.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___159_8913.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___159_8913.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8903) in
                              FStar_Syntax_Syntax.Tm_let uu____8890 in
                            mk1 uu____8889 in
                          ((M t2), uu____8883, uu____8886)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8925 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____8925 in
      let uu____8926 = check env e mn in
      match uu____8926 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8942 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8964 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____8964 in
      let uu____8965 = check env e mn in
      match uu____8965 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8981 -> failwith "[check_m]: impossible"
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
        (let uu____9011 =
           let uu____9012 = is_C c in Prims.op_Negation uu____9012 in
         if uu____9011 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____9020 =
           let uu____9021 = FStar_Syntax_Subst.compress c in
           uu____9021.FStar_Syntax_Syntax.n in
         match uu____9020 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9046 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9046 with
              | (wp_head,wp_args) ->
                  ((let uu____9084 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9098 =
                           let uu____9099 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9099 in
                         Prims.op_Negation uu____9098) in
                    if uu____9084 then failwith "mismatch" else ());
                   (let uu____9107 =
                      let uu____9108 =
                        let uu____9123 =
                          FStar_List.map2
                            (fun uu____9151  ->
                               fun uu____9152  ->
                                 match (uu____9151, uu____9152) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9189 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9189
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9192 = print_implicit q in
                                         let uu____9193 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b\n"
                                           uu____9192 uu____9193)
                                      else ();
                                      (let uu____9195 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9195, q)))) args wp_args in
                        (head1, uu____9123) in
                      FStar_Syntax_Syntax.Tm_app uu____9108 in
                    mk1 uu____9107)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9229 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9229 with
              | (binders_orig,comp1) ->
                  let uu____9236 =
                    let uu____9251 =
                      FStar_List.map
                        (fun uu____9285  ->
                           match uu____9285 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9305 = is_C h in
                               if uu____9305
                               then
                                 let w' =
                                   let uu____9317 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9317 in
                                 let uu____9318 =
                                   let uu____9325 =
                                     let uu____9332 =
                                       let uu____9337 =
                                         let uu____9338 =
                                           let uu____9339 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____9339 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9338 in
                                       (uu____9337, q) in
                                     [uu____9332] in
                                   (w', q) :: uu____9325 in
                                 (w', uu____9318)
                               else
                                 (let x =
                                    let uu____9360 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9360 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9251 in
                  (match uu____9236 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____9415 =
                           let uu____9418 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9418 in
                         FStar_Syntax_Subst.subst_comp uu____9415 comp1 in
                       let app =
                         let uu____9422 =
                           let uu____9423 =
                             let uu____9438 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9453 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____9454 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9453, uu____9454)) bvs in
                             (wp, uu____9438) in
                           FStar_Syntax_Syntax.Tm_app uu____9423 in
                         mk1 uu____9422 in
                       let comp3 =
                         let uu____9462 = type_of_comp comp2 in
                         let uu____9463 = is_monadic_comp comp2 in
                         trans_G env uu____9462 uu____9463 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9465,uu____9466) ->
             trans_F_ env e wp
         | uu____9507 -> failwith "impossible trans_F_")
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
            let uu____9512 =
              let uu____9513 = star_type' env h in
              let uu____9516 =
                let uu____9525 =
                  let uu____9530 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____9530) in
                [uu____9525] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9513;
                FStar_Syntax_Syntax.effect_args = uu____9516;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____9512
          else
            (let uu____9540 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____9540)
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
    fun t  -> let uu____9555 = n env.env t in star_type' env uu____9555
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____9572 = n env.env t in check_n env uu____9572
let trans_F:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9585 = n env.env c in
        let uu____9586 = n env.env wp in trans_F_ env uu____9585 uu____9586