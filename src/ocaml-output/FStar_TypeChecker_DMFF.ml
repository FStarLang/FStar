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
              let uu___125_104 = a in
              let uu____105 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___125_104.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___125_104.FStar_Syntax_Syntax.index);
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
                          let uu___126_2070 = t1 in
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
                              (uu___126_2070.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___126_2070.FStar_Syntax_Syntax.vars)
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
                      let uu___127_2805 = ed in
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
                          (uu___127_2805.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___127_2805.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___127_2805.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___127_2805.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___127_2805.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___127_2805.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___127_2805.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2806;
                        FStar_Syntax_Syntax.ite_wp = uu____2810;
                        FStar_Syntax_Syntax.stronger = uu____2814;
                        FStar_Syntax_Syntax.close_wp = uu____2818;
                        FStar_Syntax_Syntax.assert_p = uu____2822;
                        FStar_Syntax_Syntax.assume_p = uu____2826;
                        FStar_Syntax_Syntax.null_wp = uu____2830;
                        FStar_Syntax_Syntax.trivial = uu____2834;
                        FStar_Syntax_Syntax.repr =
                          (uu___127_2805.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___127_2805.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___127_2805.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___127_2805.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2734, uu____2804)))))
type env_ = env[@@deriving show]
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___128_2852 = dmff_env in
      {
        env = env';
        subst = (uu___128_2852.subst);
        tc_const = (uu___128_2852.tc_const)
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
  fun uu___114_2892  ->
    match uu___114_2892 with
    | FStar_Syntax_Syntax.Total (t,uu____2894) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___113_2907  ->
                match uu___113_2907 with
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
  fun uu___115_2925  ->
    match uu___115_2925 with
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
                       let uu___129_3142 = bv in
                       let uu____3143 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___129_3142.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___129_3142.FStar_Syntax_Syntax.index);
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
                 let uu___132_3627 = env in
                 let uu____3628 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3628;
                   subst = (uu___132_3627.subst);
                   tc_const = (uu___132_3627.tc_const)
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
               ((let uu___133_3648 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___133_3648.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___133_3648.FStar_Syntax_Syntax.index);
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
  fun uu___117_3942  ->
    match uu___117_3942 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___116_3949  ->
                match uu___116_3949 with
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
  fun uu___118_4191  ->
    match uu___118_4191 with
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
          let strip_m uu___119_4467 =
            match uu___119_4467 with
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
                  let uu___134_4939 = rc in
                  let uu____4940 =
                    let uu____4945 =
                      let uu____4946 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____4946 in
                    FStar_Pervasives_Native.Some uu____4945 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___134_4939.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____4940;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___134_4939.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____4938 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___135_4956 = env in
            let uu____4957 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____4957;
              subst = (uu___135_4956.subst);
              tc_const = (uu___135_4956.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____4977  ->
                 match uu____4977 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___136_4990 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___136_4990.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___136_4990.FStar_Syntax_Syntax.index);
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
                           let uu___137_5079 = bv in
                           let uu____5080 =
                             let uu____5083 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5083 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___137_5079.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___137_5079.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5080
                           } in
                         let env3 =
                           let uu___138_5085 = env2 in
                           let uu____5086 =
                             let uu____5089 =
                               let uu____5090 =
                                 let uu____5097 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5097) in
                               FStar_Syntax_Syntax.NT uu____5090 in
                             uu____5089 :: (env2.subst) in
                           {
                             env = (uu___138_5085.env);
                             subst = uu____5086;
                             tc_const = (uu___138_5085.tc_const)
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
                            let uu___139_5110 = bv in
                            let uu____5111 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___139_5110.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___139_5110.FStar_Syntax_Syntax.index);
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
                                        (fun uu___120_5214  ->
                                           match uu___120_5214 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5215 -> false)) in
                                 if uu____5210
                                 then
                                   let uu____5216 =
                                     FStar_List.filter
                                       (fun uu___121_5220  ->
                                          match uu___121_5220 with
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
                                      (fun uu___122_5234  ->
                                         match uu___122_5234 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5235 -> false)) in
                               if uu____5230
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___123_5242  ->
                                        match uu___123_5242 with
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
                                    let uu___140_5253 = rc in
                                    let uu____5254 =
                                      let uu____5259 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5259 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___140_5253.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5254;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___140_5253.FStar_Syntax_Syntax.residual_flags)
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
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____5443 = check_n env head1 in
          (match uu____5443 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____5463 =
                   let uu____5464 = FStar_Syntax_Subst.compress t in
                   uu____5464.FStar_Syntax_Syntax.n in
                 match uu____5463 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____5467 -> true
                 | uu____5480 -> false in
               let rec flatten1 t =
                 let uu____5497 =
                   let uu____5498 = FStar_Syntax_Subst.compress t in
                   uu____5498.FStar_Syntax_Syntax.n in
                 match uu____5497 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____5515);
                                FStar_Syntax_Syntax.pos = uu____5516;
                                FStar_Syntax_Syntax.vars = uu____5517;_})
                     when is_arrow t1 ->
                     let uu____5542 = flatten1 t1 in
                     (match uu____5542 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5624,uu____5625)
                     -> flatten1 e1
                 | uu____5666 ->
                     let uu____5667 =
                       let uu____5668 =
                         let uu____5669 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____5669 in
                       FStar_Errors.Err uu____5668 in
                     FStar_Exn.raise uu____5667 in
               let uu____5682 = flatten1 t_head in
               (match uu____5682 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____5742 =
                          let uu____5743 =
                            let uu____5744 = FStar_Util.string_of_int n1 in
                            let uu____5751 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____5762 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____5744 uu____5751 uu____5762 in
                          FStar_Errors.Err uu____5743 in
                        FStar_Exn.raise uu____5742)
                     else ();
                     (let uu____5770 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____5770 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____5811 args1 =
                            match uu____5811 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____5885 =
                                       let uu____5886 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____5886.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____5885
                                 | (binders3,[]) ->
                                     let uu____5916 =
                                       let uu____5917 =
                                         let uu____5920 =
                                           let uu____5921 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____5921 in
                                         FStar_Syntax_Subst.compress
                                           uu____5920 in
                                       uu____5917.FStar_Syntax_Syntax.n in
                                     (match uu____5916 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____5946 =
                                            let uu____5947 =
                                              let uu____5948 =
                                                let uu____5961 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____5961) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____5948 in
                                            mk1 uu____5947 in
                                          N uu____5946
                                      | uu____5968 -> failwith "wat?")
                                 | ([],uu____5969::uu____5970) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6010)::binders3,(arg,uu____6013)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____6066 = FStar_List.splitAt n' binders1 in
                          (match uu____6066 with
                           | (binders2,uu____6098) ->
                               let uu____6123 =
                                 let uu____6142 =
                                   FStar_List.map2
                                     (fun uu____6190  ->
                                        fun uu____6191  ->
                                          match (uu____6190, uu____6191) with
                                          | ((bv,uu____6223),(arg,q)) ->
                                              let uu____6234 =
                                                let uu____6235 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____6235.FStar_Syntax_Syntax.n in
                                              (match uu____6234 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____6252 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____6276 ->
                                                   let uu____6277 =
                                                     check_n env arg in
                                                   (match uu____6277 with
                                                    | (uu____6298,s_arg,u_arg)
                                                        ->
                                                        let uu____6301 =
                                                          let uu____6308 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____6308
                                                          then
                                                            let uu____6315 =
                                                              let uu____6320
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____6320, q) in
                                                            [uu____6315;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____6301))))
                                     binders2 args in
                                 FStar_List.split uu____6142 in
                               (match uu____6123 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____6409 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____6418 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____6409, uu____6418)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6484) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____6490) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6496,uu____6497) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____6539 = let uu____6540 = env.tc_const c in N uu____6540 in
          (uu____6539, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____6541 ->
          let uu____6554 =
            let uu____6555 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____6555 in
          failwith uu____6554
      | FStar_Syntax_Syntax.Tm_type uu____6562 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____6569 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____6588 ->
          let uu____6595 =
            let uu____6596 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____6596 in
          failwith uu____6595
      | FStar_Syntax_Syntax.Tm_uvar uu____6603 ->
          let uu____6620 =
            let uu____6621 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____6621 in
          failwith uu____6620
      | FStar_Syntax_Syntax.Tm_delayed uu____6628 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6659 =
            let uu____6660 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____6660 in
          failwith uu____6659
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
          let uu____6705 = check_n env e0 in
          match uu____6705 with
          | (uu____6718,s_e0,u_e0) ->
              let uu____6721 =
                let uu____6750 =
                  FStar_List.map
                    (fun b  ->
                       let uu____6811 = FStar_Syntax_Subst.open_branch b in
                       match uu____6811 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___141_6853 = env in
                             let uu____6854 =
                               let uu____6855 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____6855 in
                             {
                               env = uu____6854;
                               subst = (uu___141_6853.subst);
                               tc_const = (uu___141_6853.tc_const)
                             } in
                           let uu____6858 = f env1 body in
                           (match uu____6858 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____6930 ->
                           FStar_Exn.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____6750 in
              (match uu____6721 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7032 = FStar_List.hd nms in
                     match uu____7032 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___124_7038  ->
                          match uu___124_7038 with
                          | M uu____7039 -> true
                          | uu____7040 -> false) nms in
                   let uu____7041 =
                     let uu____7078 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____7168  ->
                              match uu____7168 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____7345 =
                                         check env original_body (M t2) in
                                       (match uu____7345 with
                                        | (uu____7382,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____7421,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____7078 in
                   (match uu____7041 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____7605  ->
                                 match uu____7605 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____7656 =
                                         let uu____7657 =
                                           let uu____7672 =
                                             let uu____7679 =
                                               let uu____7684 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____7685 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____7684, uu____7685) in
                                             [uu____7679] in
                                           (s_body, uu____7672) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____7657 in
                                       mk1 uu____7656 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____7717 =
                              let uu____7718 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____7718] in
                            let uu____7719 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____7717 uu____7719
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____7725 =
                              let uu____7732 =
                                let uu____7733 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____7733 in
                              [uu____7732] in
                            let uu____7734 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____7725 uu____7734 in
                          let uu____7737 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____7776 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____7737, uu____7776)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____7793 =
                             let uu____7796 =
                               let uu____7797 =
                                 let uu____7824 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____7824,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____7797 in
                             mk1 uu____7796 in
                           let uu____7861 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____7793, uu____7861))))
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
              let uu____7908 = FStar_Syntax_Syntax.mk_binder x in
              [uu____7908] in
            let uu____7909 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____7909 with
            | (x_binders1,e21) ->
                let uu____7922 = infer env e1 in
                (match uu____7922 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____7939 = is_C t1 in
                       if uu____7939
                       then
                         let uu___142_7940 = binding in
                         let uu____7941 =
                           let uu____7944 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____7944 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___142_7940.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___142_7940.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____7941;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___142_7940.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___142_7940.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___143_7947 = env in
                       let uu____7948 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___144_7950 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___144_7950.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___144_7950.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____7948;
                         subst = (uu___143_7947.subst);
                         tc_const = (uu___143_7947.tc_const)
                       } in
                     let uu____7951 = proceed env1 e21 in
                     (match uu____7951 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___145_7968 = binding in
                            let uu____7969 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___145_7968.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___145_7968.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____7969;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___145_7968.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___145_7968.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____7972 =
                            let uu____7975 =
                              let uu____7976 =
                                let uu____7989 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___146_7999 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___146_7999.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___146_7999.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___146_7999.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___146_7999.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____7989) in
                              FStar_Syntax_Syntax.Tm_let uu____7976 in
                            mk1 uu____7975 in
                          let uu____8000 =
                            let uu____8003 =
                              let uu____8004 =
                                let uu____8017 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___147_8027 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___147_8027.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___147_8027.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___147_8027.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___147_8027.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8017) in
                              FStar_Syntax_Syntax.Tm_let uu____8004 in
                            mk1 uu____8003 in
                          (nm_rec, uu____7972, uu____8000))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___148_8036 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___148_8036.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___148_8036.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___148_8036.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___149_8038 = env in
                       let uu____8039 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___150_8041 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___150_8041.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___150_8041.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8039;
                         subst = (uu___149_8038.subst);
                         tc_const = (uu___149_8038.tc_const)
                       } in
                     let uu____8042 = ensure_m env1 e21 in
                     (match uu____8042 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____8065 =
                              let uu____8066 =
                                let uu____8081 =
                                  let uu____8088 =
                                    let uu____8093 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____8094 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8093, uu____8094) in
                                  [uu____8088] in
                                (s_e2, uu____8081) in
                              FStar_Syntax_Syntax.Tm_app uu____8066 in
                            mk1 uu____8065 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____8113 =
                              let uu____8114 =
                                let uu____8129 =
                                  let uu____8136 =
                                    let uu____8141 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____8141) in
                                  [uu____8136] in
                                (s_e1, uu____8129) in
                              FStar_Syntax_Syntax.Tm_app uu____8114 in
                            mk1 uu____8113 in
                          let uu____8156 =
                            let uu____8157 =
                              let uu____8158 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8158] in
                            FStar_Syntax_Util.abs uu____8157 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____8159 =
                            let uu____8162 =
                              let uu____8163 =
                                let uu____8176 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___151_8186 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___151_8186.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___151_8186.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___151_8186.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___151_8186.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8176) in
                              FStar_Syntax_Syntax.Tm_let uu____8163 in
                            mk1 uu____8162 in
                          ((M t2), uu____8156, uu____8159)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8198 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____8198 in
      let uu____8199 = check env e mn in
      match uu____8199 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8215 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8237 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____8237 in
      let uu____8238 = check env e mn in
      match uu____8238 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8254 -> failwith "[check_m]: impossible"
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
        (let uu____8284 =
           let uu____8285 = is_C c in Prims.op_Negation uu____8285 in
         if uu____8284 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____8293 =
           let uu____8294 = FStar_Syntax_Subst.compress c in
           uu____8294.FStar_Syntax_Syntax.n in
         match uu____8293 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____8319 = FStar_Syntax_Util.head_and_args wp in
             (match uu____8319 with
              | (wp_head,wp_args) ->
                  ((let uu____8357 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____8371 =
                           let uu____8372 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____8372 in
                         Prims.op_Negation uu____8371) in
                    if uu____8357 then failwith "mismatch" else ());
                   (let uu____8380 =
                      let uu____8381 =
                        let uu____8396 =
                          FStar_List.map2
                            (fun uu____8424  ->
                               fun uu____8425  ->
                                 match (uu____8424, uu____8425) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____8462 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____8462
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____8465 = print_implicit q in
                                         let uu____8466 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b\n"
                                           uu____8465 uu____8466)
                                      else ();
                                      (let uu____8468 =
                                         trans_F_ env arg wp_arg in
                                       (uu____8468, q)))) args wp_args in
                        (head1, uu____8396) in
                      FStar_Syntax_Syntax.Tm_app uu____8381 in
                    mk1 uu____8380)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____8502 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____8502 with
              | (binders_orig,comp1) ->
                  let uu____8509 =
                    let uu____8524 =
                      FStar_List.map
                        (fun uu____8558  ->
                           match uu____8558 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____8578 = is_C h in
                               if uu____8578
                               then
                                 let w' =
                                   let uu____8590 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____8590 in
                                 let uu____8591 =
                                   let uu____8598 =
                                     let uu____8605 =
                                       let uu____8610 =
                                         let uu____8611 =
                                           let uu____8612 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____8612 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____8611 in
                                       (uu____8610, q) in
                                     [uu____8605] in
                                   (w', q) :: uu____8598 in
                                 (w', uu____8591)
                               else
                                 (let x =
                                    let uu____8633 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____8633 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____8524 in
                  (match uu____8509 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____8688 =
                           let uu____8691 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____8691 in
                         FStar_Syntax_Subst.subst_comp uu____8688 comp1 in
                       let app =
                         let uu____8695 =
                           let uu____8696 =
                             let uu____8711 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____8726 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____8727 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8726, uu____8727)) bvs in
                             (wp, uu____8711) in
                           FStar_Syntax_Syntax.Tm_app uu____8696 in
                         mk1 uu____8695 in
                       let comp3 =
                         let uu____8735 = type_of_comp comp2 in
                         let uu____8736 = is_monadic_comp comp2 in
                         trans_G env uu____8735 uu____8736 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____8738,uu____8739) ->
             trans_F_ env e wp
         | uu____8780 -> failwith "impossible trans_F_")
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
            let uu____8785 =
              let uu____8786 = star_type' env h in
              let uu____8789 =
                let uu____8798 =
                  let uu____8803 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____8803) in
                [uu____8798] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____8786;
                FStar_Syntax_Syntax.effect_args = uu____8789;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____8785
          else
            (let uu____8813 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____8813)
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
    fun t  -> let uu____8828 = n env.env t in star_type' env uu____8828
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____8845 = n env.env t in check_n env uu____8845
let trans_F:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____8858 = n env.env c in
        let uu____8859 = n env.env wp in trans_F_ env uu____8858 uu____8859