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
              let uu___73_93 = a in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___73_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___73_93.FStar_Syntax_Syntax.index);
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
                  (fun uu____376  ->
                     match uu____376 with
                     | (t,b) ->
                         let uu____387 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____387)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____418 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____418)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____441 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____441) in
              let uu____442 =
                let uu____457 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____479 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____479 in
                    let uu____482 =
                      let uu____483 =
                        let uu____490 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____491 =
                          let uu____494 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____494] in
                        uu____490 :: uu____491 in
                      FStar_List.append binders uu____483 in
                    FStar_Syntax_Util.abs uu____482 body
                      FStar_Pervasives_Native.None in
                  let uu____499 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____500 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____499, uu____500) in
                match uu____457 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____534 =
                        let uu____535 =
                          let uu____550 =
                            let uu____557 =
                              FStar_List.map
                                (fun uu____577  ->
                                   match uu____577 with
                                   | (bv,uu____587) ->
                                       let uu____588 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____589 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____588, uu____589)) binders in
                            let uu____590 =
                              let uu____597 =
                                let uu____602 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____603 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____602, uu____603) in
                              let uu____604 =
                                let uu____611 =
                                  let uu____616 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____616) in
                                [uu____611] in
                              uu____597 :: uu____604 in
                            FStar_List.append uu____557 uu____590 in
                          (fv, uu____550) in
                        FStar_Syntax_Syntax.Tm_app uu____535 in
                      mk1 uu____534 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____442 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____675 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____675 in
                    let ret1 =
                      let uu____679 =
                        let uu____680 =
                          let uu____683 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____683 in
                        FStar_Syntax_Util.residual_tot uu____680 in
                      FStar_Pervasives_Native.Some uu____679 in
                    let body =
                      let uu____685 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____685 ret1 in
                    let uu____686 =
                      let uu____687 = mk_all_implicit binders in
                      let uu____694 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____687 uu____694 in
                    FStar_Syntax_Util.abs uu____686 body ret1 in
                  let c_pure1 =
                    let uu____722 = mk_lid "pure" in
                    register env1 uu____722 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____727 =
                        let uu____728 =
                          let uu____729 =
                            let uu____736 =
                              let uu____737 =
                                let uu____738 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____738 in
                              FStar_Syntax_Syntax.mk_binder uu____737 in
                            [uu____736] in
                          let uu____739 =
                            let uu____742 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____742 in
                          FStar_Syntax_Util.arrow uu____729 uu____739 in
                        mk_gctx uu____728 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____727 in
                    let r =
                      let uu____744 =
                        let uu____745 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____745 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____744 in
                    let ret1 =
                      let uu____749 =
                        let uu____750 =
                          let uu____753 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____753 in
                        FStar_Syntax_Util.residual_tot uu____750 in
                      FStar_Pervasives_Native.Some uu____749 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____761 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____764 =
                          let uu____773 =
                            let uu____776 =
                              let uu____777 =
                                let uu____778 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____778
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____777 in
                            [uu____776] in
                          FStar_List.append gamma_as_args uu____773 in
                        FStar_Syntax_Util.mk_app uu____761 uu____764 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____781 =
                      let uu____782 = mk_all_implicit binders in
                      let uu____789 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____782 uu____789 in
                    FStar_Syntax_Util.abs uu____781 outer_body ret1 in
                  let c_app1 =
                    let uu____825 = mk_lid "app" in
                    register env1 uu____825 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____832 =
                        let uu____839 =
                          let uu____840 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____840 in
                        [uu____839] in
                      let uu____841 =
                        let uu____844 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____844 in
                      FStar_Syntax_Util.arrow uu____832 uu____841 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____847 =
                        let uu____848 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____848 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____847 in
                    let ret1 =
                      let uu____852 =
                        let uu____853 =
                          let uu____856 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____856 in
                        FStar_Syntax_Util.residual_tot uu____853 in
                      FStar_Pervasives_Native.Some uu____852 in
                    let uu____857 =
                      let uu____858 = mk_all_implicit binders in
                      let uu____865 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____858 uu____865 in
                    let uu____900 =
                      let uu____901 =
                        let uu____910 =
                          let uu____913 =
                            let uu____916 =
                              let uu____925 =
                                let uu____928 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____928] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____925 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____916 in
                          let uu____929 =
                            let uu____934 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____934] in
                          uu____913 :: uu____929 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____910 in
                      FStar_Syntax_Util.mk_app c_app1 uu____901 in
                    FStar_Syntax_Util.abs uu____857 uu____900 ret1 in
                  let c_lift11 =
                    let uu____938 = mk_lid "lift1" in
                    register env1 uu____938 c_lift1 in
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
                      let uu____946 =
                        let uu____953 =
                          let uu____954 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____954 in
                        let uu____955 =
                          let uu____958 =
                            let uu____959 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____959 in
                          [uu____958] in
                        uu____953 :: uu____955 in
                      let uu____960 =
                        let uu____963 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____963 in
                      FStar_Syntax_Util.arrow uu____946 uu____960 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____966 =
                        let uu____967 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____967 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____966 in
                    let a2 =
                      let uu____969 =
                        let uu____970 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____970 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____969 in
                    let ret1 =
                      let uu____974 =
                        let uu____975 =
                          let uu____978 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____978 in
                        FStar_Syntax_Util.residual_tot uu____975 in
                      FStar_Pervasives_Native.Some uu____974 in
                    let uu____979 =
                      let uu____980 = mk_all_implicit binders in
                      let uu____987 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____980 uu____987 in
                    let uu____1030 =
                      let uu____1031 =
                        let uu____1040 =
                          let uu____1043 =
                            let uu____1046 =
                              let uu____1055 =
                                let uu____1058 =
                                  let uu____1061 =
                                    let uu____1070 =
                                      let uu____1073 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1073] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1070 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1061 in
                                let uu____1074 =
                                  let uu____1079 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1079] in
                                uu____1058 :: uu____1074 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1055 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1046 in
                          let uu____1082 =
                            let uu____1087 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1087] in
                          uu____1043 :: uu____1082 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1040 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1031 in
                    FStar_Syntax_Util.abs uu____979 uu____1030 ret1 in
                  let c_lift21 =
                    let uu____1091 = mk_lid "lift2" in
                    register env1 uu____1091 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1098 =
                        let uu____1105 =
                          let uu____1106 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1106 in
                        [uu____1105] in
                      let uu____1107 =
                        let uu____1110 =
                          let uu____1111 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1111 in
                        FStar_Syntax_Syntax.mk_Total uu____1110 in
                      FStar_Syntax_Util.arrow uu____1098 uu____1107 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1116 =
                        let uu____1117 =
                          let uu____1120 =
                            let uu____1121 =
                              let uu____1128 =
                                let uu____1129 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1129 in
                              [uu____1128] in
                            let uu____1130 =
                              let uu____1133 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1133 in
                            FStar_Syntax_Util.arrow uu____1121 uu____1130 in
                          mk_ctx uu____1120 in
                        FStar_Syntax_Util.residual_tot uu____1117 in
                      FStar_Pervasives_Native.Some uu____1116 in
                    let e1 =
                      let uu____1135 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1135 in
                    let body =
                      let uu____1137 =
                        let uu____1138 =
                          let uu____1145 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1145] in
                        FStar_List.append gamma uu____1138 in
                      let uu____1150 =
                        let uu____1151 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1154 =
                          let uu____1163 =
                            let uu____1164 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1164 in
                          let uu____1165 = args_of_binders1 gamma in
                          uu____1163 :: uu____1165 in
                        FStar_Syntax_Util.mk_app uu____1151 uu____1154 in
                      FStar_Syntax_Util.abs uu____1137 uu____1150 ret1 in
                    let uu____1168 =
                      let uu____1169 = mk_all_implicit binders in
                      let uu____1176 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1169 uu____1176 in
                    FStar_Syntax_Util.abs uu____1168 body ret1 in
                  let c_push1 =
                    let uu____1208 = mk_lid "push" in
                    register env1 uu____1208 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1228 =
                        let uu____1229 =
                          let uu____1244 = args_of_binders1 binders in
                          (c, uu____1244) in
                        FStar_Syntax_Syntax.Tm_app uu____1229 in
                      mk1 uu____1228
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1254 =
                        let uu____1255 =
                          let uu____1262 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1263 =
                            let uu____1266 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1266] in
                          uu____1262 :: uu____1263 in
                        let uu____1267 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1255 uu____1267 in
                      FStar_Syntax_Syntax.mk_Total uu____1254 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1271 =
                      let uu____1272 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1272 in
                    let uu____1283 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1285 =
                        let uu____1288 =
                          let uu____1297 =
                            let uu____1300 =
                              let uu____1303 =
                                let uu____1312 =
                                  let uu____1313 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1313 in
                                [uu____1312] in
                              FStar_Syntax_Util.mk_app l_ite uu____1303 in
                            [uu____1300] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1297 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1288 in
                      FStar_Syntax_Util.ascribe uu____1285
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1271 uu____1283
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1333 = mk_lid "wp_if_then_else" in
                    register env1 uu____1333 wp_if_then_else in
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
                      let uu____1344 =
                        let uu____1353 =
                          let uu____1356 =
                            let uu____1359 =
                              let uu____1368 =
                                let uu____1371 =
                                  let uu____1374 =
                                    let uu____1383 =
                                      let uu____1384 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1384 in
                                    [uu____1383] in
                                  FStar_Syntax_Util.mk_app l_and uu____1374 in
                                [uu____1371] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1368 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1359 in
                          let uu____1389 =
                            let uu____1394 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1394] in
                          uu____1356 :: uu____1389 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1353 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1344 in
                    let uu____1397 =
                      let uu____1398 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1398 in
                    FStar_Syntax_Util.abs uu____1397 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1410 = mk_lid "wp_assert" in
                    register env1 uu____1410 wp_assert in
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
                      let uu____1421 =
                        let uu____1430 =
                          let uu____1433 =
                            let uu____1436 =
                              let uu____1445 =
                                let uu____1448 =
                                  let uu____1451 =
                                    let uu____1460 =
                                      let uu____1461 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1461 in
                                    [uu____1460] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1451 in
                                [uu____1448] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1445 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1436 in
                          let uu____1466 =
                            let uu____1471 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1471] in
                          uu____1433 :: uu____1466 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1430 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1421 in
                    let uu____1474 =
                      let uu____1475 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1475 in
                    FStar_Syntax_Util.abs uu____1474 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1487 = mk_lid "wp_assume" in
                    register env1 uu____1487 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1496 =
                        let uu____1503 =
                          let uu____1504 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1504 in
                        [uu____1503] in
                      let uu____1505 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1496 uu____1505 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1512 =
                        let uu____1521 =
                          let uu____1524 =
                            let uu____1527 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1527 in
                          let uu____1536 =
                            let uu____1541 =
                              let uu____1544 =
                                let uu____1553 =
                                  let uu____1556 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1556] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1553 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1544 in
                            [uu____1541] in
                          uu____1524 :: uu____1536 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1521 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1512 in
                    let uu____1563 =
                      let uu____1564 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1564 in
                    FStar_Syntax_Util.abs uu____1563 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1576 = mk_lid "wp_close" in
                    register env1 uu____1576 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1586 =
                      let uu____1587 =
                        let uu____1588 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1588 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1587 in
                    FStar_Pervasives_Native.Some uu____1586 in
                  let mk_forall1 x body =
                    let uu____1600 =
                      let uu____1603 =
                        let uu____1604 =
                          let uu____1619 =
                            let uu____1622 =
                              let uu____1623 =
                                let uu____1624 =
                                  let uu____1625 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1625] in
                                FStar_Syntax_Util.abs uu____1624 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1623 in
                            [uu____1622] in
                          (FStar_Syntax_Util.tforall, uu____1619) in
                        FStar_Syntax_Syntax.Tm_app uu____1604 in
                      FStar_Syntax_Syntax.mk uu____1603 in
                    uu____1600 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1635 =
                      let uu____1636 = FStar_Syntax_Subst.compress t in
                      uu____1636.FStar_Syntax_Syntax.n in
                    match uu____1635 with
                    | FStar_Syntax_Syntax.Tm_type uu____1639 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1665  ->
                              match uu____1665 with
                              | (b,uu____1671) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1672 -> true in
                  let rec is_monotonic t =
                    let uu____1677 =
                      let uu____1678 = FStar_Syntax_Subst.compress t in
                      uu____1678.FStar_Syntax_Syntax.n in
                    match uu____1677 with
                    | FStar_Syntax_Syntax.Tm_type uu____1681 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1707  ->
                              match uu____1707 with
                              | (b,uu____1713) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1714 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1766 =
                      let uu____1767 = FStar_Syntax_Subst.compress t1 in
                      uu____1767.FStar_Syntax_Syntax.n in
                    match uu____1766 with
                    | FStar_Syntax_Syntax.Tm_type uu____1770 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1773);
                                      FStar_Syntax_Syntax.pos = uu____1774;
                                      FStar_Syntax_Syntax.vars = uu____1775;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1809 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1809
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1812 =
                              let uu____1815 =
                                let uu____1824 =
                                  let uu____1825 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1825 in
                                [uu____1824] in
                              FStar_Syntax_Util.mk_app x uu____1815 in
                            let uu____1826 =
                              let uu____1829 =
                                let uu____1838 =
                                  let uu____1839 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1839 in
                                [uu____1838] in
                              FStar_Syntax_Util.mk_app y uu____1829 in
                            mk_rel1 b uu____1812 uu____1826 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1844 =
                               let uu____1845 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1848 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1845 uu____1848 in
                             let uu____1851 =
                               let uu____1852 =
                                 let uu____1855 =
                                   let uu____1864 =
                                     let uu____1865 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1865 in
                                   [uu____1864] in
                                 FStar_Syntax_Util.mk_app x uu____1855 in
                               let uu____1866 =
                                 let uu____1869 =
                                   let uu____1878 =
                                     let uu____1879 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1879 in
                                   [uu____1878] in
                                 FStar_Syntax_Util.mk_app y uu____1869 in
                               mk_rel1 b uu____1852 uu____1866 in
                             FStar_Syntax_Util.mk_imp uu____1844 uu____1851 in
                           let uu____1880 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1880)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1883);
                                      FStar_Syntax_Syntax.pos = uu____1884;
                                      FStar_Syntax_Syntax.vars = uu____1885;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1919 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1919
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1922 =
                              let uu____1925 =
                                let uu____1934 =
                                  let uu____1935 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1935 in
                                [uu____1934] in
                              FStar_Syntax_Util.mk_app x uu____1925 in
                            let uu____1936 =
                              let uu____1939 =
                                let uu____1948 =
                                  let uu____1949 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1949 in
                                [uu____1948] in
                              FStar_Syntax_Util.mk_app y uu____1939 in
                            mk_rel1 b uu____1922 uu____1936 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1954 =
                               let uu____1955 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1958 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1955 uu____1958 in
                             let uu____1961 =
                               let uu____1962 =
                                 let uu____1965 =
                                   let uu____1974 =
                                     let uu____1975 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1975 in
                                   [uu____1974] in
                                 FStar_Syntax_Util.mk_app x uu____1965 in
                               let uu____1976 =
                                 let uu____1979 =
                                   let uu____1988 =
                                     let uu____1989 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1989 in
                                   [uu____1988] in
                                 FStar_Syntax_Util.mk_app y uu____1979 in
                               mk_rel1 b uu____1962 uu____1976 in
                             FStar_Syntax_Util.mk_imp uu____1954 uu____1961 in
                           let uu____1990 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1990)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___74_2021 = t1 in
                          let uu____2022 =
                            let uu____2023 =
                              let uu____2036 =
                                let uu____2037 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2037 in
                              ([binder], uu____2036) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2023 in
                          {
                            FStar_Syntax_Syntax.n = uu____2022;
                            FStar_Syntax_Syntax.pos =
                              (uu___74_2021.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___74_2021.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2052 ->
                        failwith "unhandled arrow"
                    | uu____2065 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2080 =
                        let uu____2081 = FStar_Syntax_Subst.compress t1 in
                        uu____2081.FStar_Syntax_Syntax.n in
                      match uu____2080 with
                      | FStar_Syntax_Syntax.Tm_type uu____2084 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2107 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2107
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2122 =
                                let uu____2123 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2123 i in
                              FStar_Syntax_Syntax.fvar uu____2122
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2150 =
                            let uu____2157 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2171  ->
                                     match uu____2171 with
                                     | (t2,q) ->
                                         let uu____2178 = project i x in
                                         let uu____2179 = project i y in
                                         mk_stronger t2 uu____2178 uu____2179)
                                args in
                            match uu____2157 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2150 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2206);
                                      FStar_Syntax_Syntax.pos = uu____2207;
                                      FStar_Syntax_Syntax.vars = uu____2208;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2246  ->
                                   match uu____2246 with
                                   | (bv,q) ->
                                       let uu____2253 =
                                         let uu____2254 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2254 in
                                       FStar_Syntax_Syntax.gen_bv uu____2253
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2261 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2261) bvs in
                          let body =
                            let uu____2263 = FStar_Syntax_Util.mk_app x args in
                            let uu____2264 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2263 uu____2264 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2271);
                                      FStar_Syntax_Syntax.pos = uu____2272;
                                      FStar_Syntax_Syntax.vars = uu____2273;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2311  ->
                                   match uu____2311 with
                                   | (bv,q) ->
                                       let uu____2318 =
                                         let uu____2319 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2319 in
                                       FStar_Syntax_Syntax.gen_bv uu____2318
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2326 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2326) bvs in
                          let body =
                            let uu____2328 = FStar_Syntax_Util.mk_app x args in
                            let uu____2329 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2328 uu____2329 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2334 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2336 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2337 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2338 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2336 uu____2337 uu____2338 in
                    let uu____2339 =
                      let uu____2340 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2340 in
                    FStar_Syntax_Util.abs uu____2339 body ret_tot_type in
                  let stronger1 =
                    let uu____2368 = mk_lid "stronger" in
                    register env1 uu____2368 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2374 = FStar_Util.prefix gamma in
                    match uu____2374 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2419 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2419 in
                          let uu____2422 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2422 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2432 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2432 in
                              let guard_free1 =
                                let uu____2442 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2442 in
                              let pat =
                                let uu____2446 =
                                  let uu____2455 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2455] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2446 in
                              let pattern_guarded_body =
                                let uu____2459 =
                                  let uu____2460 =
                                    let uu____2467 =
                                      let uu____2468 =
                                        let uu____2479 =
                                          let uu____2482 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2482] in
                                        [uu____2479] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2468 in
                                    (body, uu____2467) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2460 in
                                mk1 uu____2459 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2487 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2491 =
                            let uu____2492 =
                              let uu____2493 =
                                let uu____2494 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2497 =
                                  let uu____2506 = args_of_binders1 wp_args in
                                  let uu____2509 =
                                    let uu____2512 =
                                      let uu____2513 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2513 in
                                    [uu____2512] in
                                  FStar_List.append uu____2506 uu____2509 in
                                FStar_Syntax_Util.mk_app uu____2494
                                  uu____2497 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2493 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2492 in
                          FStar_Syntax_Util.abs gamma uu____2491
                            ret_gtot_type in
                        let uu____2514 =
                          let uu____2515 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2515 in
                        FStar_Syntax_Util.abs uu____2514 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2527 = mk_lid "wp_ite" in
                    register env1 uu____2527 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2533 = FStar_Util.prefix gamma in
                    match uu____2533 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2576 =
                            let uu____2577 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2580 =
                              let uu____2589 =
                                let uu____2590 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2590 in
                              [uu____2589] in
                            FStar_Syntax_Util.mk_app uu____2577 uu____2580 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2576 in
                        let uu____2591 =
                          let uu____2592 =
                            let uu____2599 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2599 gamma in
                          FStar_List.append binders uu____2592 in
                        FStar_Syntax_Util.abs uu____2591 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2615 = mk_lid "null_wp" in
                    register env1 uu____2615 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2624 =
                        let uu____2633 =
                          let uu____2636 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2637 =
                            let uu____2640 =
                              let uu____2643 =
                                let uu____2652 =
                                  let uu____2653 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2653 in
                                [uu____2652] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2643 in
                            let uu____2654 =
                              let uu____2659 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2659] in
                            uu____2640 :: uu____2654 in
                          uu____2636 :: uu____2637 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2633 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2624 in
                    let uu____2662 =
                      let uu____2663 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2663 in
                    FStar_Syntax_Util.abs uu____2662 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2675 = mk_lid "wp_trivial" in
                    register env1 uu____2675 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2680 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2680
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2685 =
                      let uu____2688 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____2688 in
                    let uu____2736 =
                      let uu___75_2737 = ed in
                      let uu____2738 =
                        let uu____2739 = c wp_if_then_else2 in
                        ([], uu____2739) in
                      let uu____2742 =
                        let uu____2743 = c wp_ite2 in ([], uu____2743) in
                      let uu____2746 =
                        let uu____2747 = c stronger2 in ([], uu____2747) in
                      let uu____2750 =
                        let uu____2751 = c wp_close2 in ([], uu____2751) in
                      let uu____2754 =
                        let uu____2755 = c wp_assert2 in ([], uu____2755) in
                      let uu____2758 =
                        let uu____2759 = c wp_assume2 in ([], uu____2759) in
                      let uu____2762 =
                        let uu____2763 = c null_wp2 in ([], uu____2763) in
                      let uu____2766 =
                        let uu____2767 = c wp_trivial2 in ([], uu____2767) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___75_2737.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___75_2737.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___75_2737.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___75_2737.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___75_2737.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___75_2737.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___75_2737.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2738;
                        FStar_Syntax_Syntax.ite_wp = uu____2742;
                        FStar_Syntax_Syntax.stronger = uu____2746;
                        FStar_Syntax_Syntax.close_wp = uu____2750;
                        FStar_Syntax_Syntax.assert_p = uu____2754;
                        FStar_Syntax_Syntax.assume_p = uu____2758;
                        FStar_Syntax_Syntax.null_wp = uu____2762;
                        FStar_Syntax_Syntax.trivial = uu____2766;
                        FStar_Syntax_Syntax.repr =
                          (uu___75_2737.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___75_2737.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___75_2737.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___75_2737.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2685, uu____2736)))))
type env_ = env[@@deriving show]
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___76_2781 = dmff_env in
      {
        env = env';
        subst = (uu___76_2781.subst);
        tc_const = (uu___76_2781.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ[@@deriving show]
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2794 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2806 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm[@@deriving show]
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___62_2816  ->
    match uu___62_2816 with
    | FStar_Syntax_Syntax.Total (t,uu____2818) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___61_2831  ->
                match uu___61_2831 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2832 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2834 =
          let uu____2835 =
            let uu____2836 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2836 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2835 in
        failwith uu____2834
    | FStar_Syntax_Syntax.GTotal uu____2837 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___63_2848  ->
    match uu___63_2848 with
    | N t ->
        let uu____2850 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2850
    | M t ->
        let uu____2852 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2852
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2856,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2858;
                      FStar_Syntax_Syntax.vars = uu____2859;_})
        -> nm_of_comp n2
    | uu____2876 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____2884 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____2884 with | M uu____2885 -> true | N uu____2886 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2890 -> false
let double_star: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ  ->
    let star_once typ1 =
      let uu____2900 =
        let uu____2907 =
          let uu____2908 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2908 in
        [uu____2907] in
      let uu____2909 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2900 uu____2909 in
    let uu____2912 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2912
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
          (let uu____2949 =
             let uu____2962 =
               let uu____2969 =
                 let uu____2974 =
                   let uu____2975 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2975 in
                 let uu____2976 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2974, uu____2976) in
               [uu____2969] in
             let uu____2985 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2962, uu____2985) in
           FStar_Syntax_Syntax.Tm_arrow uu____2949)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3013) ->
          let binders1 =
            FStar_List.map
              (fun uu____3049  ->
                 match uu____3049 with
                 | (bv,aqual) ->
                     let uu____3060 =
                       let uu___77_3061 = bv in
                       let uu____3062 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___77_3061.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___77_3061.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3062
                       } in
                     (uu____3060, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3065,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3067);
                             FStar_Syntax_Syntax.pos = uu____3068;
                             FStar_Syntax_Syntax.vars = uu____3069;_})
               ->
               let uu____3094 =
                 let uu____3095 =
                   let uu____3108 =
                     let uu____3109 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3109 in
                   (binders1, uu____3108) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3095 in
               mk1 uu____3094
           | uu____3116 ->
               let uu____3117 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3117 with
                | N hn ->
                    let uu____3119 =
                      let uu____3120 =
                        let uu____3133 =
                          let uu____3134 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3134 in
                        (binders1, uu____3133) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3120 in
                    mk1 uu____3119
                | M a ->
                    let uu____3142 =
                      let uu____3143 =
                        let uu____3156 =
                          let uu____3163 =
                            let uu____3170 =
                              let uu____3175 =
                                let uu____3176 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3176 in
                              let uu____3177 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3175, uu____3177) in
                            [uu____3170] in
                          FStar_List.append binders1 uu____3163 in
                        let uu____3190 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3156, uu____3190) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3143 in
                    mk1 uu____3142))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3260 = f x in
                    FStar_Util.string_builder_append strb uu____3260);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3267 = f x1 in
                         FStar_Util.string_builder_append strb uu____3267))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3269 =
              let uu____3274 =
                let uu____3275 = FStar_Syntax_Print.term_to_string t2 in
                let uu____3276 =
                  string_of_set FStar_Syntax_Print.bv_to_string s in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3275 uu____3276 in
              (FStar_Errors.Warning_DependencyFound, uu____3274) in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3269 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3284 =
              let uu____3285 = FStar_Syntax_Subst.compress ty in
              uu____3285.FStar_Syntax_Syntax.n in
            match uu____3284 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3306 =
                  let uu____3307 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3307 in
                if uu____3306
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3333 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3333 s in
                       let uu____3336 =
                         let uu____3337 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3337 in
                       if uu____3336
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else () in
                     let uu____3340 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3340 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3362  ->
                                  match uu____3362 with
                                  | (bv,uu____3372) ->
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
            | uu____3386 ->
                ((let uu____3388 =
                    let uu____3393 =
                      let uu____3394 = FStar_Syntax_Print.term_to_string ty in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3394 in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3393) in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3388);
                 false) in
          let rec is_valid_application head2 =
            let uu____3399 =
              let uu____3400 = FStar_Syntax_Subst.compress head2 in
              uu____3400.FStar_Syntax_Syntax.n in
            match uu____3399 with
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
                  (let uu____3405 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3405)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3407 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3407 with
                 | ((uu____3416,ty),uu____3418) ->
                     let uu____3423 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3423
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3431 -> true
                        | uu____3446 ->
                            ((let uu____3448 =
                                let uu____3453 =
                                  let uu____3454 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3454 in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3453) in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3448);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3456 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3457 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3459) ->
                is_valid_application t2
            | uu____3464 -> false in
          let uu____3465 = is_valid_application head1 in
          if uu____3465
          then
            let uu____3466 =
              let uu____3467 =
                let uu____3482 =
                  FStar_List.map
                    (fun uu____3503  ->
                       match uu____3503 with
                       | (t2,qual) ->
                           let uu____3520 = star_type' env t2 in
                           (uu____3520, qual)) args in
                (head1, uu____3482) in
              FStar_Syntax_Syntax.Tm_app uu____3467 in
            mk1 uu____3466
          else
            (let uu____3530 =
               let uu____3535 =
                 let uu____3536 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3536 in
               (FStar_Errors.Fatal_WrongTerm, uu____3535) in
             FStar_Errors.raise_err uu____3530)
      | FStar_Syntax_Syntax.Tm_bvar uu____3537 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3538 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3539 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3540 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3564 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3564 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___80_3572 = env in
                 let uu____3573 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3573;
                   subst = (uu___80_3572.subst);
                   tc_const = (uu___80_3572.tc_const)
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
               ((let uu___81_3593 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___81_3593.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___81_3593.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3600 =
            let uu____3601 =
              let uu____3608 = star_type' env t2 in (uu____3608, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3601 in
          mk1 uu____3600
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3656 =
            let uu____3657 =
              let uu____3684 = star_type' env e in
              let uu____3685 =
                let uu____3700 =
                  let uu____3707 = star_type' env t2 in
                  FStar_Util.Inl uu____3707 in
                (uu____3700, FStar_Pervasives_Native.None) in
              (uu____3684, uu____3685, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3657 in
          mk1 uu____3656
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3785 =
            let uu____3786 =
              let uu____3813 = star_type' env e in
              let uu____3814 =
                let uu____3829 =
                  let uu____3836 =
                    star_type' env (FStar_Syntax_Util.comp_result c) in
                  FStar_Util.Inl uu____3836 in
                (uu____3829, FStar_Pervasives_Native.None) in
              (uu____3813, uu____3814, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3786 in
          mk1 uu____3785
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____3867,(uu____3868,FStar_Pervasives_Native.Some uu____3869),uu____3870)
          ->
          let uu____3919 =
            let uu____3924 =
              let uu____3925 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____3925 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3924) in
          FStar_Errors.raise_err uu____3919
      | FStar_Syntax_Syntax.Tm_refine uu____3926 ->
          let uu____3933 =
            let uu____3938 =
              let uu____3939 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3939 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3938) in
          FStar_Errors.raise_err uu____3933
      | FStar_Syntax_Syntax.Tm_uinst uu____3940 ->
          let uu____3947 =
            let uu____3952 =
              let uu____3953 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3953 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3952) in
          FStar_Errors.raise_err uu____3947
      | FStar_Syntax_Syntax.Tm_constant uu____3954 ->
          let uu____3955 =
            let uu____3960 =
              let uu____3961 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3961 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3960) in
          FStar_Errors.raise_err uu____3955
      | FStar_Syntax_Syntax.Tm_match uu____3962 ->
          let uu____3985 =
            let uu____3990 =
              let uu____3991 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3991 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____3990) in
          FStar_Errors.raise_err uu____3985
      | FStar_Syntax_Syntax.Tm_let uu____3992 ->
          let uu____4005 =
            let uu____4010 =
              let uu____4011 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4011 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4010) in
          FStar_Errors.raise_err uu____4005
      | FStar_Syntax_Syntax.Tm_uvar uu____4012 ->
          let uu____4029 =
            let uu____4034 =
              let uu____4035 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4035 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4034) in
          FStar_Errors.raise_err uu____4029
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4036 =
            let uu____4041 =
              let uu____4042 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4042 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4041) in
          FStar_Errors.raise_err uu____4036
      | FStar_Syntax_Syntax.Tm_delayed uu____4043 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___65_4072  ->
    match uu___65_4072 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___64_4079  ->
                match uu___64_4079 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4080 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____4084 =
      let uu____4085 = FStar_Syntax_Subst.compress t in
      uu____4085.FStar_Syntax_Syntax.n in
    match uu____4084 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4111 =
            let uu____4112 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____4112 in
          is_C uu____4111 in
        if r
        then
          ((let uu____4128 =
              let uu____4129 =
                FStar_List.for_all
                  (fun uu____4137  ->
                     match uu____4137 with | (h,uu____4143) -> is_C h) args in
              Prims.op_Negation uu____4129 in
            if uu____4128 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4147 =
              let uu____4148 =
                FStar_List.for_all
                  (fun uu____4157  ->
                     match uu____4157 with
                     | (h,uu____4163) ->
                         let uu____4164 = is_C h in
                         Prims.op_Negation uu____4164) args in
              Prims.op_Negation uu____4148 in
            if uu____4147 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4184 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4184 with
         | M t1 ->
             ((let uu____4187 = is_C t1 in
               if uu____4187 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4191) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4197) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4203,uu____4204) -> is_C t1
    | uu____4245 -> false
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
          let uu____4268 =
            let uu____4269 =
              let uu____4284 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4285 =
                let uu____4292 =
                  let uu____4297 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4297) in
                [uu____4292] in
              (uu____4284, uu____4285) in
            FStar_Syntax_Syntax.Tm_app uu____4269 in
          mk1 uu____4268 in
        let uu____4312 =
          let uu____4313 = FStar_Syntax_Syntax.mk_binder p in [uu____4313] in
        FStar_Syntax_Util.abs uu____4312 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___66_4316  ->
    match uu___66_4316 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4317 -> false
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
        let return_if uu____4492 =
          match uu____4492 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4519 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4521 =
                       let uu____4522 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4522 in
                     Prims.op_Negation uu____4521) in
                if uu____4519
                then
                  let uu____4523 =
                    let uu____4528 =
                      let uu____4529 = FStar_Syntax_Print.term_to_string e in
                      let uu____4530 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4531 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4529 uu____4530 uu____4531 in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4528) in
                  FStar_Errors.raise_err uu____4523
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4548 = mk_return env t1 s_e in
                     ((M t1), uu____4548, u_e)))
               | (M t1,N t2) ->
                   let uu____4551 =
                     let uu____4556 =
                       let uu____4557 = FStar_Syntax_Print.term_to_string e in
                       let uu____4558 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4559 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4557 uu____4558 uu____4559 in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4556) in
                   FStar_Errors.raise_err uu____4551) in
        let ensure_m env1 e2 =
          let strip_m uu___67_4600 =
            match uu___67_4600 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4616 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4636 =
                let uu____4641 =
                  let uu____4642 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4642 in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4641) in
              FStar_Errors.raise_error uu____4636 e2.FStar_Syntax_Syntax.pos
          | M uu____4649 ->
              let uu____4650 = check env1 e2 context_nm in strip_m uu____4650 in
        let uu____4657 =
          let uu____4658 = FStar_Syntax_Subst.compress e in
          uu____4658.FStar_Syntax_Syntax.n in
        match uu____4657 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4667 ->
            let uu____4668 = infer env e in return_if uu____4668
        | FStar_Syntax_Syntax.Tm_name uu____4675 ->
            let uu____4676 = infer env e in return_if uu____4676
        | FStar_Syntax_Syntax.Tm_fvar uu____4683 ->
            let uu____4684 = infer env e in return_if uu____4684
        | FStar_Syntax_Syntax.Tm_abs uu____4691 ->
            let uu____4708 = infer env e in return_if uu____4708
        | FStar_Syntax_Syntax.Tm_constant uu____4715 ->
            let uu____4716 = infer env e in return_if uu____4716
        | FStar_Syntax_Syntax.Tm_app uu____4723 ->
            let uu____4738 = infer env e in return_if uu____4738
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4806) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4812) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4818,uu____4819) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4860 ->
            let uu____4873 =
              let uu____4874 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4874 in
            failwith uu____4873
        | FStar_Syntax_Syntax.Tm_type uu____4881 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4888 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4907 ->
            let uu____4914 =
              let uu____4915 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4915 in
            failwith uu____4914
        | FStar_Syntax_Syntax.Tm_uvar uu____4922 ->
            let uu____4939 =
              let uu____4940 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4940 in
            failwith uu____4939
        | FStar_Syntax_Syntax.Tm_delayed uu____4947 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4978 =
              let uu____4979 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4979 in
            failwith uu____4978
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
      let uu____5003 =
        let uu____5004 = FStar_Syntax_Subst.compress e in
        uu____5004.FStar_Syntax_Syntax.n in
      match uu____5003 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5063;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5064;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5070 =
                  let uu___82_5071 = rc in
                  let uu____5072 =
                    let uu____5077 =
                      let uu____5078 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____5078 in
                    FStar_Pervasives_Native.Some uu____5077 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___82_5071.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5072;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___82_5071.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____5070 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___83_5088 = env in
            let uu____5089 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____5089;
              subst = (uu___83_5088.subst);
              tc_const = (uu___83_5088.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____5109  ->
                 match uu____5109 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___84_5122 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___84_5122.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___84_5122.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____5123 =
            FStar_List.fold_left
              (fun uu____5152  ->
                 fun uu____5153  ->
                   match (uu____5152, uu____5153) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5201 = is_C c in
                       if uu____5201
                       then
                         let xw =
                           let uu____5209 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5209 in
                         let x =
                           let uu___85_5211 = bv in
                           let uu____5212 =
                             let uu____5215 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5215 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___85_5211.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___85_5211.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5212
                           } in
                         let env3 =
                           let uu___86_5217 = env2 in
                           let uu____5218 =
                             let uu____5221 =
                               let uu____5222 =
                                 let uu____5229 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5229) in
                               FStar_Syntax_Syntax.NT uu____5222 in
                             uu____5221 :: (env2.subst) in
                           {
                             env = (uu___86_5217.env);
                             subst = uu____5218;
                             tc_const = (uu___86_5217.tc_const)
                           } in
                         let uu____5230 =
                           let uu____5233 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5234 =
                             let uu____5237 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5237 :: acc in
                           uu____5233 :: uu____5234 in
                         (env3, uu____5230)
                       else
                         (let x =
                            let uu___87_5242 = bv in
                            let uu____5243 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___87_5242.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___87_5242.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5243
                            } in
                          let uu____5246 =
                            let uu____5249 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5249 :: acc in
                          (env2, uu____5246))) (env1, []) binders1 in
          (match uu____5123 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5269 =
                 let check_what =
                   let uu____5287 = is_monadic rc_opt1 in
                   if uu____5287 then check_m else check_n in
                 let uu____5299 = check_what env2 body1 in
                 match uu____5299 with
                 | (t,s_body,u_body) ->
                     let uu____5315 =
                       let uu____5316 =
                         let uu____5317 = is_monadic rc_opt1 in
                         if uu____5317 then M t else N t in
                       comp_of_nm uu____5316 in
                     (uu____5315, s_body, u_body) in
               (match uu____5269 with
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
                                 let uu____5342 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___68_5346  ->
                                           match uu___68_5346 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5347 -> false)) in
                                 if uu____5342
                                 then
                                   let uu____5348 =
                                     FStar_List.filter
                                       (fun uu___69_5352  ->
                                          match uu___69_5352 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5353 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5348
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5362 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___70_5366  ->
                                         match uu___70_5366 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5367 -> false)) in
                               if uu____5362
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___71_5374  ->
                                        match uu___71_5374 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5375 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5376 =
                                   let uu____5377 =
                                     let uu____5382 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5382 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5377 flags1 in
                                 FStar_Pervasives_Native.Some uu____5376
                               else
                                 (let uu____5384 =
                                    let uu___88_5385 = rc in
                                    let uu____5386 =
                                      let uu____5391 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5391 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___88_5385.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5386;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___88_5385.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5384)) in
                    let uu____5392 =
                      let comp1 =
                        let uu____5402 = is_monadic rc_opt1 in
                        let uu____5403 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5402 uu____5403 in
                      let uu____5404 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5404,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5392 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5446 =
                             let uu____5447 =
                               let uu____5464 =
                                 let uu____5467 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5467 s_rc_opt in
                               (s_binders1, s_body1, uu____5464) in
                             FStar_Syntax_Syntax.Tm_abs uu____5447 in
                           mk1 uu____5446 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5477 =
                             let uu____5478 =
                               let uu____5495 =
                                 let uu____5498 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5498 u_rc_opt in
                               (u_binders2, u_body2, uu____5495) in
                             FStar_Syntax_Syntax.Tm_abs uu____5478 in
                           mk1 uu____5477 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5508;_};
            FStar_Syntax_Syntax.fv_delta = uu____5509;
            FStar_Syntax_Syntax.fv_qual = uu____5510;_}
          ->
          let uu____5513 =
            let uu____5518 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5518 in
          (match uu____5513 with
           | (uu____5549,t) ->
               let uu____5551 = let uu____5552 = normalize1 t in N uu____5552 in
               (uu____5551, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5553;
             FStar_Syntax_Syntax.vars = uu____5554;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5617 = FStar_Syntax_Util.head_and_args e in
          (match uu____5617 with
           | (unary_op,uu____5639) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5698;
             FStar_Syntax_Syntax.vars = uu____5699;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5775 = FStar_Syntax_Util.head_and_args e in
          (match uu____5775 with
           | (unary_op,uu____5797) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5862;
             FStar_Syntax_Syntax.vars = uu____5863;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____5901 = infer env a in
          (match uu____5901 with
           | (t,s,u) ->
               let uu____5917 = FStar_Syntax_Util.head_and_args e in
               (match uu____5917 with
                | (head1,uu____5939) ->
                    let uu____5960 =
                      let uu____5961 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____5961 in
                    let uu____5962 =
                      let uu____5965 =
                        let uu____5966 =
                          let uu____5981 =
                            let uu____5984 = FStar_Syntax_Syntax.as_arg s in
                            [uu____5984] in
                          (head1, uu____5981) in
                        FStar_Syntax_Syntax.Tm_app uu____5966 in
                      mk1 uu____5965 in
                    let uu____5989 =
                      let uu____5992 =
                        let uu____5993 =
                          let uu____6008 =
                            let uu____6011 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6011] in
                          (head1, uu____6008) in
                        FStar_Syntax_Syntax.Tm_app uu____5993 in
                      mk1 uu____5992 in
                    (uu____5960, uu____5962, uu____5989)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6020;
             FStar_Syntax_Syntax.vars = uu____6021;_},(a1,uu____6023)::a2::[])
          ->
          let uu____6065 = infer env a1 in
          (match uu____6065 with
           | (t,s,u) ->
               let uu____6081 = FStar_Syntax_Util.head_and_args e in
               (match uu____6081 with
                | (head1,uu____6103) ->
                    let uu____6124 =
                      let uu____6127 =
                        let uu____6128 =
                          let uu____6143 =
                            let uu____6146 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6146; a2] in
                          (head1, uu____6143) in
                        FStar_Syntax_Syntax.Tm_app uu____6128 in
                      mk1 uu____6127 in
                    let uu____6163 =
                      let uu____6166 =
                        let uu____6167 =
                          let uu____6182 =
                            let uu____6185 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6185; a2] in
                          (head1, uu____6182) in
                        FStar_Syntax_Syntax.Tm_app uu____6167 in
                      mk1 uu____6166 in
                    (t, uu____6124, uu____6163)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6206;
             FStar_Syntax_Syntax.vars = uu____6207;_},uu____6208)
          ->
          let uu____6229 =
            let uu____6234 =
              let uu____6235 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6235 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6234) in
          FStar_Errors.raise_error uu____6229 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6242;
             FStar_Syntax_Syntax.vars = uu____6243;_},uu____6244)
          ->
          let uu____6265 =
            let uu____6270 =
              let uu____6271 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6271 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6270) in
          FStar_Errors.raise_error uu____6265 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6300 = check_n env head1 in
          (match uu____6300 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6320 =
                   let uu____6321 = FStar_Syntax_Subst.compress t in
                   uu____6321.FStar_Syntax_Syntax.n in
                 match uu____6320 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6324 -> true
                 | uu____6337 -> false in
               let rec flatten1 t =
                 let uu____6354 =
                   let uu____6355 = FStar_Syntax_Subst.compress t in
                   uu____6355.FStar_Syntax_Syntax.n in
                 match uu____6354 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6372);
                                FStar_Syntax_Syntax.pos = uu____6373;
                                FStar_Syntax_Syntax.vars = uu____6374;_})
                     when is_arrow t1 ->
                     let uu____6399 = flatten1 t1 in
                     (match uu____6399 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6481,uu____6482)
                     -> flatten1 e1
                 | uu____6523 ->
                     let uu____6524 =
                       let uu____6529 =
                         let uu____6530 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6530 in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6529) in
                     FStar_Errors.raise_err uu____6524 in
               let uu____6543 = flatten1 t_head in
               (match uu____6543 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6603 =
                          let uu____6608 =
                            let uu____6609 = FStar_Util.string_of_int n1 in
                            let uu____6616 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____6627 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6609 uu____6616 uu____6627 in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6608) in
                        FStar_Errors.raise_err uu____6603)
                     else ();
                     (let uu____6635 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____6635 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6676 args1 =
                            match uu____6676 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6750 =
                                       let uu____6751 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____6751.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____6750
                                 | (binders3,[]) ->
                                     let uu____6781 =
                                       let uu____6782 =
                                         let uu____6785 =
                                           let uu____6786 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6786 in
                                         FStar_Syntax_Subst.compress
                                           uu____6785 in
                                       uu____6782.FStar_Syntax_Syntax.n in
                                     (match uu____6781 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6811 =
                                            let uu____6812 =
                                              let uu____6813 =
                                                let uu____6826 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____6826) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6813 in
                                            mk1 uu____6812 in
                                          N uu____6811
                                      | uu____6833 -> failwith "wat?")
                                 | ([],uu____6834::uu____6835) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6875)::binders3,(arg,uu____6878)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____6931 = FStar_List.splitAt n' binders1 in
                          (match uu____6931 with
                           | (binders2,uu____6963) ->
                               let uu____6988 =
                                 let uu____7007 =
                                   FStar_List.map2
                                     (fun uu____7055  ->
                                        fun uu____7056  ->
                                          match (uu____7055, uu____7056) with
                                          | ((bv,uu____7088),(arg,q)) ->
                                              let uu____7099 =
                                                let uu____7100 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____7100.FStar_Syntax_Syntax.n in
                                              (match uu____7099 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7117 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____7141 ->
                                                   let uu____7142 =
                                                     check_n env arg in
                                                   (match uu____7142 with
                                                    | (uu____7163,s_arg,u_arg)
                                                        ->
                                                        let uu____7166 =
                                                          let uu____7173 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7173
                                                          then
                                                            let uu____7180 =
                                                              let uu____7185
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7185, q) in
                                                            [uu____7180;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7166))))
                                     binders2 args in
                                 FStar_List.split uu____7007 in
                               (match uu____6988 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7274 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7283 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7274, uu____7283)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7349) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7355) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7361,uu____7362) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7404 = let uu____7405 = env.tc_const c in N uu____7405 in
          (uu____7404, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7406 ->
          let uu____7419 =
            let uu____7420 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7420 in
          failwith uu____7419
      | FStar_Syntax_Syntax.Tm_type uu____7427 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7434 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7453 ->
          let uu____7460 =
            let uu____7461 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7461 in
          failwith uu____7460
      | FStar_Syntax_Syntax.Tm_uvar uu____7468 ->
          let uu____7485 =
            let uu____7486 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7486 in
          failwith uu____7485
      | FStar_Syntax_Syntax.Tm_delayed uu____7493 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7524 =
            let uu____7525 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7525 in
          failwith uu____7524
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
          let uu____7570 = check_n env e0 in
          match uu____7570 with
          | (uu____7583,s_e0,u_e0) ->
              let uu____7586 =
                let uu____7615 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7676 = FStar_Syntax_Subst.open_branch b in
                       match uu____7676 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___89_7718 = env in
                             let uu____7719 =
                               let uu____7720 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7720 in
                             {
                               env = uu____7719;
                               subst = (uu___89_7718.subst);
                               tc_const = (uu___89_7718.tc_const)
                             } in
                           let uu____7723 = f env1 body in
                           (match uu____7723 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7795 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____7615 in
              (match uu____7586 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7897 = FStar_List.hd nms in
                     match uu____7897 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___72_7903  ->
                          match uu___72_7903 with
                          | M uu____7904 -> true
                          | uu____7905 -> false) nms in
                   let uu____7906 =
                     let uu____7943 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8033  ->
                              match uu____8033 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8210 =
                                         check env original_body (M t2) in
                                       (match uu____8210 with
                                        | (uu____8247,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8286,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____7943 in
                   (match uu____7906 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8470  ->
                                 match uu____8470 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8521 =
                                         let uu____8522 =
                                           let uu____8537 =
                                             let uu____8544 =
                                               let uu____8549 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____8550 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____8549, uu____8550) in
                                             [uu____8544] in
                                           (s_body, uu____8537) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8522 in
                                       mk1 uu____8521 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____8582 =
                              let uu____8583 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8583] in
                            let uu____8584 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____8582 uu____8584
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____8590 =
                              let uu____8597 =
                                let uu____8598 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8598 in
                              [uu____8597] in
                            let uu____8599 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____8590 uu____8599 in
                          let uu____8602 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____8641 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____8602, uu____8641)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____8658 =
                             let uu____8661 =
                               let uu____8662 =
                                 let uu____8689 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____8689,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8662 in
                             mk1 uu____8661 in
                           let uu____8726 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____8658, uu____8726))))
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
              let uu____8773 = FStar_Syntax_Syntax.mk_binder x in
              [uu____8773] in
            let uu____8774 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____8774 with
            | (x_binders1,e21) ->
                let uu____8787 = infer env e1 in
                (match uu____8787 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____8804 = is_C t1 in
                       if uu____8804
                       then
                         let uu___90_8805 = binding in
                         let uu____8806 =
                           let uu____8809 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____8809 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___90_8805.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___90_8805.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____8806;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___90_8805.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___90_8805.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___91_8812 = env in
                       let uu____8813 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___92_8815 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___92_8815.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___92_8815.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8813;
                         subst = (uu___91_8812.subst);
                         tc_const = (uu___91_8812.tc_const)
                       } in
                     let uu____8816 = proceed env1 e21 in
                     (match uu____8816 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___93_8833 = binding in
                            let uu____8834 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___93_8833.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___93_8833.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____8834;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___93_8833.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___93_8833.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____8837 =
                            let uu____8840 =
                              let uu____8841 =
                                let uu____8854 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___94_8864 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___94_8864.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___94_8864.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___94_8864.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___94_8864.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____8854) in
                              FStar_Syntax_Syntax.Tm_let uu____8841 in
                            mk1 uu____8840 in
                          let uu____8865 =
                            let uu____8868 =
                              let uu____8869 =
                                let uu____8882 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___95_8892 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___95_8892.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___95_8892.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___95_8892.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___95_8892.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8882) in
                              FStar_Syntax_Syntax.Tm_let uu____8869 in
                            mk1 uu____8868 in
                          (nm_rec, uu____8837, uu____8865))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___96_8901 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___96_8901.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___96_8901.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___96_8901.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___97_8903 = env in
                       let uu____8904 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___98_8906 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___98_8906.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___98_8906.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8904;
                         subst = (uu___97_8903.subst);
                         tc_const = (uu___97_8903.tc_const)
                       } in
                     let uu____8907 = ensure_m env1 e21 in
                     (match uu____8907 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____8930 =
                              let uu____8931 =
                                let uu____8946 =
                                  let uu____8953 =
                                    let uu____8958 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____8959 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8958, uu____8959) in
                                  [uu____8953] in
                                (s_e2, uu____8946) in
                              FStar_Syntax_Syntax.Tm_app uu____8931 in
                            mk1 uu____8930 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____8978 =
                              let uu____8979 =
                                let uu____8994 =
                                  let uu____9001 =
                                    let uu____9006 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____9006) in
                                  [uu____9001] in
                                (s_e1, uu____8994) in
                              FStar_Syntax_Syntax.Tm_app uu____8979 in
                            mk1 uu____8978 in
                          let uu____9021 =
                            let uu____9022 =
                              let uu____9023 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____9023] in
                            FStar_Syntax_Util.abs uu____9022 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____9024 =
                            let uu____9027 =
                              let uu____9028 =
                                let uu____9041 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___99_9051 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___99_9051.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___99_9051.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___99_9051.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___99_9051.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9041) in
                              FStar_Syntax_Syntax.Tm_let uu____9028 in
                            mk1 uu____9027 in
                          ((M t2), uu____9021, uu____9024)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9063 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____9063 in
      let uu____9064 = check env e mn in
      match uu____9064 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9080 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9102 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____9102 in
      let uu____9103 = check env e mn in
      match uu____9103 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9119 -> failwith "[check_m]: impossible"
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
        (let uu____9149 =
           let uu____9150 = is_C c in Prims.op_Negation uu____9150 in
         if uu____9149 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____9158 =
           let uu____9159 = FStar_Syntax_Subst.compress c in
           uu____9159.FStar_Syntax_Syntax.n in
         match uu____9158 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9184 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9184 with
              | (wp_head,wp_args) ->
                  ((let uu____9222 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9236 =
                           let uu____9237 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9237 in
                         Prims.op_Negation uu____9236) in
                    if uu____9222 then failwith "mismatch" else ());
                   (let uu____9245 =
                      let uu____9246 =
                        let uu____9261 =
                          FStar_List.map2
                            (fun uu____9289  ->
                               fun uu____9290  ->
                                 match (uu____9289, uu____9290) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9327 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9327
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9330 =
                                           let uu____9335 =
                                             let uu____9336 =
                                               print_implicit q in
                                             let uu____9337 =
                                               print_implicit q' in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %b %b\n"
                                               uu____9336 uu____9337 in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9335) in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9330)
                                      else ();
                                      (let uu____9339 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9339, q)))) args wp_args in
                        (head1, uu____9261) in
                      FStar_Syntax_Syntax.Tm_app uu____9246 in
                    mk1 uu____9245)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9373 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9373 with
              | (binders_orig,comp1) ->
                  let uu____9380 =
                    let uu____9395 =
                      FStar_List.map
                        (fun uu____9429  ->
                           match uu____9429 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9449 = is_C h in
                               if uu____9449
                               then
                                 let w' =
                                   let uu____9461 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9461 in
                                 let uu____9462 =
                                   let uu____9469 =
                                     let uu____9476 =
                                       let uu____9481 =
                                         let uu____9482 =
                                           let uu____9483 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____9483 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9482 in
                                       (uu____9481, q) in
                                     [uu____9476] in
                                   (w', q) :: uu____9469 in
                                 (w', uu____9462)
                               else
                                 (let x =
                                    let uu____9504 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9504 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9395 in
                  (match uu____9380 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____9559 =
                           let uu____9562 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9562 in
                         FStar_Syntax_Subst.subst_comp uu____9559 comp1 in
                       let app =
                         let uu____9566 =
                           let uu____9567 =
                             let uu____9582 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9597 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____9598 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9597, uu____9598)) bvs in
                             (wp, uu____9582) in
                           FStar_Syntax_Syntax.Tm_app uu____9567 in
                         mk1 uu____9566 in
                       let comp3 =
                         let uu____9606 = type_of_comp comp2 in
                         let uu____9607 = is_monadic_comp comp2 in
                         trans_G env uu____9606 uu____9607 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9609,uu____9610) ->
             trans_F_ env e wp
         | uu____9651 -> failwith "impossible trans_F_")
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
            let uu____9656 =
              let uu____9657 = star_type' env h in
              let uu____9660 =
                let uu____9669 =
                  let uu____9674 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____9674) in
                [uu____9669] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9657;
                FStar_Syntax_Syntax.effect_args = uu____9660;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____9656
          else
            (let uu____9684 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____9684)
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
    fun t  -> let uu____9695 = n env.env t in star_type' env uu____9695
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____9710 = n env.env t in check_n env uu____9710
let trans_F:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9720 = n env.env c in
        let uu____9721 = n env.env wp in trans_F_ env uu____9720 uu____9721