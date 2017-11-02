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
              let uu___350_93 = a in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___350_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___350_93.FStar_Syntax_Syntax.index);
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
                  (fun uu____414  ->
                     match uu____414 with
                     | (t,b) ->
                         let uu____425 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____425)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____456 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____456)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____479 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____479) in
              let uu____480 =
                let uu____495 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____517 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____517 in
                    let uu____520 =
                      let uu____521 =
                        let uu____528 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____529 =
                          let uu____532 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____532] in
                        uu____528 :: uu____529 in
                      FStar_List.append binders uu____521 in
                    FStar_Syntax_Util.abs uu____520 body
                      FStar_Pervasives_Native.None in
                  let uu____537 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____538 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____537, uu____538) in
                match uu____495 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____572 =
                        let uu____573 =
                          let uu____588 =
                            let uu____595 =
                              FStar_List.map
                                (fun uu____615  ->
                                   match uu____615 with
                                   | (bv,uu____625) ->
                                       let uu____626 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____627 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____626, uu____627)) binders in
                            let uu____628 =
                              let uu____635 =
                                let uu____640 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____641 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____640, uu____641) in
                              let uu____642 =
                                let uu____649 =
                                  let uu____654 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____654) in
                                [uu____649] in
                              uu____635 :: uu____642 in
                            FStar_List.append uu____595 uu____628 in
                          (fv, uu____588) in
                        FStar_Syntax_Syntax.Tm_app uu____573 in
                      mk1 uu____572 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____480 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____713 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____713 in
                    let ret1 =
                      let uu____717 =
                        let uu____718 =
                          let uu____721 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____721 in
                        FStar_Syntax_Util.residual_tot uu____718 in
                      FStar_Pervasives_Native.Some uu____717 in
                    let body =
                      let uu____723 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____723 ret1 in
                    let uu____724 =
                      let uu____725 = mk_all_implicit binders in
                      let uu____732 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____725 uu____732 in
                    FStar_Syntax_Util.abs uu____724 body ret1 in
                  let c_pure1 =
                    let uu____760 = mk_lid "pure" in
                    register env1 uu____760 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____765 =
                        let uu____766 =
                          let uu____767 =
                            let uu____774 =
                              let uu____775 =
                                let uu____776 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____776 in
                              FStar_Syntax_Syntax.mk_binder uu____775 in
                            [uu____774] in
                          let uu____777 =
                            let uu____780 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____780 in
                          FStar_Syntax_Util.arrow uu____767 uu____777 in
                        mk_gctx uu____766 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____765 in
                    let r =
                      let uu____782 =
                        let uu____783 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____783 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____782 in
                    let ret1 =
                      let uu____787 =
                        let uu____788 =
                          let uu____791 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____791 in
                        FStar_Syntax_Util.residual_tot uu____788 in
                      FStar_Pervasives_Native.Some uu____787 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____799 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____802 =
                          let uu____811 =
                            let uu____814 =
                              let uu____815 =
                                let uu____816 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____816
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____815 in
                            [uu____814] in
                          FStar_List.append gamma_as_args uu____811 in
                        FStar_Syntax_Util.mk_app uu____799 uu____802 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____819 =
                      let uu____820 = mk_all_implicit binders in
                      let uu____827 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____820 uu____827 in
                    FStar_Syntax_Util.abs uu____819 outer_body ret1 in
                  let c_app1 =
                    let uu____863 = mk_lid "app" in
                    register env1 uu____863 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____870 =
                        let uu____877 =
                          let uu____878 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____878 in
                        [uu____877] in
                      let uu____879 =
                        let uu____882 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____882 in
                      FStar_Syntax_Util.arrow uu____870 uu____879 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____885 =
                        let uu____886 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____886 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____885 in
                    let ret1 =
                      let uu____890 =
                        let uu____891 =
                          let uu____894 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____894 in
                        FStar_Syntax_Util.residual_tot uu____891 in
                      FStar_Pervasives_Native.Some uu____890 in
                    let uu____895 =
                      let uu____896 = mk_all_implicit binders in
                      let uu____903 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____896 uu____903 in
                    let uu____938 =
                      let uu____939 =
                        let uu____948 =
                          let uu____951 =
                            let uu____954 =
                              let uu____963 =
                                let uu____966 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____966] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____963 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____954 in
                          let uu____967 =
                            let uu____972 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____972] in
                          uu____951 :: uu____967 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____948 in
                      FStar_Syntax_Util.mk_app c_app1 uu____939 in
                    FStar_Syntax_Util.abs uu____895 uu____938 ret1 in
                  let c_lift11 =
                    let uu____976 = mk_lid "lift1" in
                    register env1 uu____976 c_lift1 in
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
                      let uu____984 =
                        let uu____991 =
                          let uu____992 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____992 in
                        let uu____993 =
                          let uu____996 =
                            let uu____997 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____997 in
                          [uu____996] in
                        uu____991 :: uu____993 in
                      let uu____998 =
                        let uu____1001 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____1001 in
                      FStar_Syntax_Util.arrow uu____984 uu____998 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____1004 =
                        let uu____1005 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____1005 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1004 in
                    let a2 =
                      let uu____1007 =
                        let uu____1008 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____1008 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1007 in
                    let ret1 =
                      let uu____1012 =
                        let uu____1013 =
                          let uu____1016 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____1016 in
                        FStar_Syntax_Util.residual_tot uu____1013 in
                      FStar_Pervasives_Native.Some uu____1012 in
                    let uu____1017 =
                      let uu____1018 = mk_all_implicit binders in
                      let uu____1025 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____1018 uu____1025 in
                    let uu____1068 =
                      let uu____1069 =
                        let uu____1078 =
                          let uu____1081 =
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
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1093 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1084 in
                          let uu____1120 =
                            let uu____1125 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1125] in
                          uu____1081 :: uu____1120 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1078 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1069 in
                    FStar_Syntax_Util.abs uu____1017 uu____1068 ret1 in
                  let c_lift21 =
                    let uu____1129 = mk_lid "lift2" in
                    register env1 uu____1129 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1136 =
                        let uu____1143 =
                          let uu____1144 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1144 in
                        [uu____1143] in
                      let uu____1145 =
                        let uu____1148 =
                          let uu____1149 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1149 in
                        FStar_Syntax_Syntax.mk_Total uu____1148 in
                      FStar_Syntax_Util.arrow uu____1136 uu____1145 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1154 =
                        let uu____1155 =
                          let uu____1158 =
                            let uu____1159 =
                              let uu____1166 =
                                let uu____1167 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1167 in
                              [uu____1166] in
                            let uu____1168 =
                              let uu____1171 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1171 in
                            FStar_Syntax_Util.arrow uu____1159 uu____1168 in
                          mk_ctx uu____1158 in
                        FStar_Syntax_Util.residual_tot uu____1155 in
                      FStar_Pervasives_Native.Some uu____1154 in
                    let e1 =
                      let uu____1173 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1173 in
                    let body =
                      let uu____1175 =
                        let uu____1176 =
                          let uu____1183 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1183] in
                        FStar_List.append gamma uu____1176 in
                      let uu____1188 =
                        let uu____1189 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1192 =
                          let uu____1201 =
                            let uu____1202 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1202 in
                          let uu____1203 = args_of_binders1 gamma in
                          uu____1201 :: uu____1203 in
                        FStar_Syntax_Util.mk_app uu____1189 uu____1192 in
                      FStar_Syntax_Util.abs uu____1175 uu____1188 ret1 in
                    let uu____1206 =
                      let uu____1207 = mk_all_implicit binders in
                      let uu____1214 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1207 uu____1214 in
                    FStar_Syntax_Util.abs uu____1206 body ret1 in
                  let c_push1 =
                    let uu____1246 = mk_lid "push" in
                    register env1 uu____1246 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1266 =
                        let uu____1267 =
                          let uu____1282 = args_of_binders1 binders in
                          (c, uu____1282) in
                        FStar_Syntax_Syntax.Tm_app uu____1267 in
                      mk1 uu____1266
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1292 =
                        let uu____1293 =
                          let uu____1300 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1301 =
                            let uu____1304 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1304] in
                          uu____1300 :: uu____1301 in
                        let uu____1305 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1293 uu____1305 in
                      FStar_Syntax_Syntax.mk_Total uu____1292 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1309 =
                      let uu____1310 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1310 in
                    let uu____1321 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1323 =
                        let uu____1326 =
                          let uu____1335 =
                            let uu____1338 =
                              let uu____1341 =
                                let uu____1350 =
                                  let uu____1351 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1351 in
                                [uu____1350] in
                              FStar_Syntax_Util.mk_app l_ite uu____1341 in
                            [uu____1338] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1335 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1326 in
                      FStar_Syntax_Util.ascribe uu____1323
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1309 uu____1321
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1371 = mk_lid "wp_if_then_else" in
                    register env1 uu____1371 wp_if_then_else in
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
                      let uu____1382 =
                        let uu____1391 =
                          let uu____1394 =
                            let uu____1397 =
                              let uu____1406 =
                                let uu____1409 =
                                  let uu____1412 =
                                    let uu____1421 =
                                      let uu____1422 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1422 in
                                    [uu____1421] in
                                  FStar_Syntax_Util.mk_app l_and uu____1412 in
                                [uu____1409] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1406 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1397 in
                          let uu____1427 =
                            let uu____1432 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1432] in
                          uu____1394 :: uu____1427 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1391 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1382 in
                    let uu____1435 =
                      let uu____1436 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1436 in
                    FStar_Syntax_Util.abs uu____1435 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1448 = mk_lid "wp_assert" in
                    register env1 uu____1448 wp_assert in
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
                      let uu____1459 =
                        let uu____1468 =
                          let uu____1471 =
                            let uu____1474 =
                              let uu____1483 =
                                let uu____1486 =
                                  let uu____1489 =
                                    let uu____1498 =
                                      let uu____1499 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1499 in
                                    [uu____1498] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1489 in
                                [uu____1486] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1483 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1474 in
                          let uu____1504 =
                            let uu____1509 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1509] in
                          uu____1471 :: uu____1504 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1468 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1459 in
                    let uu____1512 =
                      let uu____1513 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1513 in
                    FStar_Syntax_Util.abs uu____1512 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1525 = mk_lid "wp_assume" in
                    register env1 uu____1525 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1534 =
                        let uu____1541 =
                          let uu____1542 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1542 in
                        [uu____1541] in
                      let uu____1543 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1534 uu____1543 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1550 =
                        let uu____1559 =
                          let uu____1562 =
                            let uu____1565 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1565 in
                          let uu____1574 =
                            let uu____1579 =
                              let uu____1582 =
                                let uu____1591 =
                                  let uu____1594 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1594] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1591 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1582 in
                            [uu____1579] in
                          uu____1562 :: uu____1574 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1559 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1550 in
                    let uu____1601 =
                      let uu____1602 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1602 in
                    FStar_Syntax_Util.abs uu____1601 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1614 = mk_lid "wp_close" in
                    register env1 uu____1614 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1624 =
                      let uu____1625 =
                        let uu____1626 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1626 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1625 in
                    FStar_Pervasives_Native.Some uu____1624 in
                  let mk_forall1 x body =
                    let uu____1638 =
                      let uu____1641 =
                        let uu____1642 =
                          let uu____1657 =
                            let uu____1660 =
                              let uu____1661 =
                                let uu____1662 =
                                  let uu____1663 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1663] in
                                FStar_Syntax_Util.abs uu____1662 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1661 in
                            [uu____1660] in
                          (FStar_Syntax_Util.tforall, uu____1657) in
                        FStar_Syntax_Syntax.Tm_app uu____1642 in
                      FStar_Syntax_Syntax.mk uu____1641 in
                    uu____1638 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1673 =
                      let uu____1674 = FStar_Syntax_Subst.compress t in
                      uu____1674.FStar_Syntax_Syntax.n in
                    match uu____1673 with
                    | FStar_Syntax_Syntax.Tm_type uu____1677 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1703  ->
                              match uu____1703 with
                              | (b,uu____1709) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1710 -> true in
                  let rec is_monotonic t =
                    let uu____1715 =
                      let uu____1716 = FStar_Syntax_Subst.compress t in
                      uu____1716.FStar_Syntax_Syntax.n in
                    match uu____1715 with
                    | FStar_Syntax_Syntax.Tm_type uu____1719 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1745  ->
                              match uu____1745 with
                              | (b,uu____1751) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1752 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1804 =
                      let uu____1805 = FStar_Syntax_Subst.compress t1 in
                      uu____1805.FStar_Syntax_Syntax.n in
                    match uu____1804 with
                    | FStar_Syntax_Syntax.Tm_type uu____1808 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1811);
                                      FStar_Syntax_Syntax.pos = uu____1812;
                                      FStar_Syntax_Syntax.vars = uu____1813;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1847 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1847
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1850 =
                              let uu____1853 =
                                let uu____1862 =
                                  let uu____1863 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1863 in
                                [uu____1862] in
                              FStar_Syntax_Util.mk_app x uu____1853 in
                            let uu____1864 =
                              let uu____1867 =
                                let uu____1876 =
                                  let uu____1877 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1877 in
                                [uu____1876] in
                              FStar_Syntax_Util.mk_app y uu____1867 in
                            mk_rel1 b uu____1850 uu____1864 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1882 =
                               let uu____1883 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1886 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1883 uu____1886 in
                             let uu____1889 =
                               let uu____1890 =
                                 let uu____1893 =
                                   let uu____1902 =
                                     let uu____1903 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1903 in
                                   [uu____1902] in
                                 FStar_Syntax_Util.mk_app x uu____1893 in
                               let uu____1904 =
                                 let uu____1907 =
                                   let uu____1916 =
                                     let uu____1917 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1917 in
                                   [uu____1916] in
                                 FStar_Syntax_Util.mk_app y uu____1907 in
                               mk_rel1 b uu____1890 uu____1904 in
                             FStar_Syntax_Util.mk_imp uu____1882 uu____1889 in
                           let uu____1918 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1918)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1921);
                                      FStar_Syntax_Syntax.pos = uu____1922;
                                      FStar_Syntax_Syntax.vars = uu____1923;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1957 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1957
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
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
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1987 in
                                [uu____1986] in
                              FStar_Syntax_Util.mk_app y uu____1977 in
                            mk_rel1 b uu____1960 uu____1974 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1992 =
                               let uu____1993 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1996 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1993 uu____1996 in
                             let uu____1999 =
                               let uu____2000 =
                                 let uu____2003 =
                                   let uu____2012 =
                                     let uu____2013 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____2013 in
                                   [uu____2012] in
                                 FStar_Syntax_Util.mk_app x uu____2003 in
                               let uu____2014 =
                                 let uu____2017 =
                                   let uu____2026 =
                                     let uu____2027 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____2027 in
                                   [uu____2026] in
                                 FStar_Syntax_Util.mk_app y uu____2017 in
                               mk_rel1 b uu____2000 uu____2014 in
                             FStar_Syntax_Util.mk_imp uu____1992 uu____1999 in
                           let uu____2028 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____2028)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___351_2059 = t1 in
                          let uu____2060 =
                            let uu____2061 =
                              let uu____2074 =
                                let uu____2075 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2075 in
                              ([binder], uu____2074) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2061 in
                          {
                            FStar_Syntax_Syntax.n = uu____2060;
                            FStar_Syntax_Syntax.pos =
                              (uu___351_2059.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___351_2059.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2090 ->
                        failwith "unhandled arrow"
                    | uu____2103 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2118 =
                        let uu____2119 = FStar_Syntax_Subst.compress t1 in
                        uu____2119.FStar_Syntax_Syntax.n in
                      match uu____2118 with
                      | FStar_Syntax_Syntax.Tm_type uu____2122 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2145 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2145
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2160 =
                                let uu____2161 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2161 i in
                              FStar_Syntax_Syntax.fvar uu____2160
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2188 =
                            let uu____2195 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2209  ->
                                     match uu____2209 with
                                     | (t2,q) ->
                                         let uu____2216 = project i x in
                                         let uu____2217 = project i y in
                                         mk_stronger t2 uu____2216 uu____2217)
                                args in
                            match uu____2195 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2188 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2244);
                                      FStar_Syntax_Syntax.pos = uu____2245;
                                      FStar_Syntax_Syntax.vars = uu____2246;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2284  ->
                                   match uu____2284 with
                                   | (bv,q) ->
                                       let uu____2291 =
                                         let uu____2292 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2292 in
                                       FStar_Syntax_Syntax.gen_bv uu____2291
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2299 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2299) bvs in
                          let body =
                            let uu____2301 = FStar_Syntax_Util.mk_app x args in
                            let uu____2302 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2301 uu____2302 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2309);
                                      FStar_Syntax_Syntax.pos = uu____2310;
                                      FStar_Syntax_Syntax.vars = uu____2311;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2349  ->
                                   match uu____2349 with
                                   | (bv,q) ->
                                       let uu____2356 =
                                         let uu____2357 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2357 in
                                       FStar_Syntax_Syntax.gen_bv uu____2356
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2364 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2364) bvs in
                          let body =
                            let uu____2366 = FStar_Syntax_Util.mk_app x args in
                            let uu____2367 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2366 uu____2367 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2372 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2374 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2375 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2376 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2374 uu____2375 uu____2376 in
                    let uu____2377 =
                      let uu____2378 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2378 in
                    FStar_Syntax_Util.abs uu____2377 body ret_tot_type in
                  let stronger1 =
                    let uu____2406 = mk_lid "stronger" in
                    register env1 uu____2406 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2412 = FStar_Util.prefix gamma in
                    match uu____2412 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2457 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2457 in
                          let uu____2460 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2460 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2470 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2470 in
                              let guard_free1 =
                                let uu____2480 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2480 in
                              let pat =
                                let uu____2484 =
                                  let uu____2493 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2493] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2484 in
                              let pattern_guarded_body =
                                let uu____2497 =
                                  let uu____2498 =
                                    let uu____2505 =
                                      let uu____2506 =
                                        let uu____2517 =
                                          let uu____2520 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2520] in
                                        [uu____2517] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2506 in
                                    (body, uu____2505) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2498 in
                                mk1 uu____2497 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2525 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2529 =
                            let uu____2530 =
                              let uu____2531 =
                                let uu____2532 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2535 =
                                  let uu____2544 = args_of_binders1 wp_args in
                                  let uu____2547 =
                                    let uu____2550 =
                                      let uu____2551 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2551 in
                                    [uu____2550] in
                                  FStar_List.append uu____2544 uu____2547 in
                                FStar_Syntax_Util.mk_app uu____2532
                                  uu____2535 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2531 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2530 in
                          FStar_Syntax_Util.abs gamma uu____2529
                            ret_gtot_type in
                        let uu____2552 =
                          let uu____2553 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2553 in
                        FStar_Syntax_Util.abs uu____2552 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2565 = mk_lid "wp_ite" in
                    register env1 uu____2565 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2571 = FStar_Util.prefix gamma in
                    match uu____2571 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2614 =
                            let uu____2615 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2618 =
                              let uu____2627 =
                                let uu____2628 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2628 in
                              [uu____2627] in
                            FStar_Syntax_Util.mk_app uu____2615 uu____2618 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2614 in
                        let uu____2629 =
                          let uu____2630 =
                            let uu____2637 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2637 gamma in
                          FStar_List.append binders uu____2630 in
                        FStar_Syntax_Util.abs uu____2629 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2653 = mk_lid "null_wp" in
                    register env1 uu____2653 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2662 =
                        let uu____2671 =
                          let uu____2674 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2675 =
                            let uu____2678 =
                              let uu____2681 =
                                let uu____2690 =
                                  let uu____2691 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2691 in
                                [uu____2690] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2681 in
                            let uu____2692 =
                              let uu____2697 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2697] in
                            uu____2678 :: uu____2692 in
                          uu____2674 :: uu____2675 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2671 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2662 in
                    let uu____2700 =
                      let uu____2701 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2701 in
                    FStar_Syntax_Util.abs uu____2700 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2713 = mk_lid "wp_trivial" in
                    register env1 uu____2713 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2718 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2718
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2723 =
                      let uu____2726 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____2726 in
                    let uu____2793 =
                      let uu___352_2794 = ed in
                      let uu____2795 =
                        let uu____2796 = c wp_if_then_else2 in
                        ([], uu____2796) in
                      let uu____2799 =
                        let uu____2800 = c wp_ite2 in ([], uu____2800) in
                      let uu____2803 =
                        let uu____2804 = c stronger2 in ([], uu____2804) in
                      let uu____2807 =
                        let uu____2808 = c wp_close2 in ([], uu____2808) in
                      let uu____2811 =
                        let uu____2812 = c wp_assert2 in ([], uu____2812) in
                      let uu____2815 =
                        let uu____2816 = c wp_assume2 in ([], uu____2816) in
                      let uu____2819 =
                        let uu____2820 = c null_wp2 in ([], uu____2820) in
                      let uu____2823 =
                        let uu____2824 = c wp_trivial2 in ([], uu____2824) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___352_2794.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___352_2794.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___352_2794.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___352_2794.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___352_2794.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___352_2794.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___352_2794.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2795;
                        FStar_Syntax_Syntax.ite_wp = uu____2799;
                        FStar_Syntax_Syntax.stronger = uu____2803;
                        FStar_Syntax_Syntax.close_wp = uu____2807;
                        FStar_Syntax_Syntax.assert_p = uu____2811;
                        FStar_Syntax_Syntax.assume_p = uu____2815;
                        FStar_Syntax_Syntax.null_wp = uu____2819;
                        FStar_Syntax_Syntax.trivial = uu____2823;
                        FStar_Syntax_Syntax.repr =
                          (uu___352_2794.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___352_2794.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___352_2794.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___352_2794.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2723, uu____2793)))))
type env_ = env[@@deriving show]
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___353_2838 = dmff_env in
      {
        env = env';
        subst = (uu___353_2838.subst);
        tc_const = (uu___353_2838.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ[@@deriving show]
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2851 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2863 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm[@@deriving show]
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___339_2873  ->
    match uu___339_2873 with
    | FStar_Syntax_Syntax.Total (t,uu____2875) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___338_2888  ->
                match uu___338_2888 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2889 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2891 =
          let uu____2892 =
            let uu____2893 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2893 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2892 in
        failwith uu____2891
    | FStar_Syntax_Syntax.GTotal uu____2894 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___340_2905  ->
    match uu___340_2905 with
    | N t ->
        let uu____2907 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2907
    | M t ->
        let uu____2909 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2909
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2913,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2915;
                      FStar_Syntax_Syntax.vars = uu____2916;_})
        -> nm_of_comp n2
    | uu____2933 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____2941 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____2941 with | M uu____2942 -> true | N uu____2943 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2947 -> false
let double_star: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ  ->
    let star_once typ1 =
      let uu____2957 =
        let uu____2964 =
          let uu____2965 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2965 in
        [uu____2964] in
      let uu____2966 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2957 uu____2966 in
    let uu____2969 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2969
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
          (let uu____3006 =
             let uu____3019 =
               let uu____3026 =
                 let uu____3031 =
                   let uu____3032 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____3032 in
                 let uu____3033 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____3031, uu____3033) in
               [uu____3026] in
             let uu____3042 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____3019, uu____3042) in
           FStar_Syntax_Syntax.Tm_arrow uu____3006)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3070) ->
          let binders1 =
            FStar_List.map
              (fun uu____3106  ->
                 match uu____3106 with
                 | (bv,aqual) ->
                     let uu____3117 =
                       let uu___354_3118 = bv in
                       let uu____3119 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___354_3118.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___354_3118.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3119
                       } in
                     (uu____3117, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3122,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3124);
                             FStar_Syntax_Syntax.pos = uu____3125;
                             FStar_Syntax_Syntax.vars = uu____3126;_})
               ->
               let uu____3151 =
                 let uu____3152 =
                   let uu____3165 =
                     let uu____3166 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3166 in
                   (binders1, uu____3165) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3152 in
               mk1 uu____3151
           | uu____3173 ->
               let uu____3174 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3174 with
                | N hn ->
                    let uu____3176 =
                      let uu____3177 =
                        let uu____3190 =
                          let uu____3191 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3191 in
                        (binders1, uu____3190) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3177 in
                    mk1 uu____3176
                | M a ->
                    let uu____3199 =
                      let uu____3200 =
                        let uu____3213 =
                          let uu____3220 =
                            let uu____3227 =
                              let uu____3232 =
                                let uu____3233 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3233 in
                              let uu____3234 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3232, uu____3234) in
                            [uu____3227] in
                          FStar_List.append binders1 uu____3220 in
                        let uu____3247 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3213, uu____3247) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3200 in
                    mk1 uu____3199))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3313 = f x in
                    FStar_Util.string_builder_append strb uu____3313);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3320 = f x1 in
                         FStar_Util.string_builder_append strb uu____3320))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3322 = FStar_Syntax_Print.term_to_string t2 in
            let uu____3323 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____3322 uu____3323 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3331 =
              let uu____3332 = FStar_Syntax_Subst.compress ty in
              uu____3332.FStar_Syntax_Syntax.n in
            match uu____3331 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3353 =
                  let uu____3354 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3354 in
                if uu____3353
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3380 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3380 s in
                       let uu____3383 =
                         let uu____3384 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3384 in
                       if uu____3383
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else () in
                     let uu____3387 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3387 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3409  ->
                                  match uu____3409 with
                                  | (bv,uu____3419) ->
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
            | uu____3433 ->
                ((let uu____3435 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____3435);
                 false) in
          let rec is_valid_application head2 =
            let uu____3440 =
              let uu____3441 = FStar_Syntax_Subst.compress head2 in
              uu____3441.FStar_Syntax_Syntax.n in
            match uu____3440 with
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
                  (let uu____3446 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3446)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3448 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3448 with
                 | ((uu____3457,ty),uu____3459) ->
                     let uu____3464 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3464
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3472 -> true
                        | uu____3487 ->
                            ((let uu____3489 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____3489);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3491 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3492 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3494) ->
                is_valid_application t2
            | uu____3499 -> false in
          let uu____3500 = is_valid_application head1 in
          if uu____3500
          then
            let uu____3501 =
              let uu____3502 =
                let uu____3517 =
                  FStar_List.map
                    (fun uu____3538  ->
                       match uu____3538 with
                       | (t2,qual) ->
                           let uu____3555 = star_type' env t2 in
                           (uu____3555, qual)) args in
                (head1, uu____3517) in
              FStar_Syntax_Syntax.Tm_app uu____3502 in
            mk1 uu____3501
          else
            (let uu____3565 =
               let uu____3566 =
                 let uu____3567 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3567 in
               FStar_Errors.Err uu____3566 in
             FStar_Exn.raise uu____3565)
      | FStar_Syntax_Syntax.Tm_bvar uu____3568 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3569 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3570 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3571 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3595 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3595 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___357_3603 = env in
                 let uu____3604 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3604;
                   subst = (uu___357_3603.subst);
                   tc_const = (uu___357_3603.tc_const)
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
               ((let uu___358_3624 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___358_3624.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___358_3624.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3631 =
            let uu____3632 =
              let uu____3639 = star_type' env t2 in (uu____3639, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3632 in
          mk1 uu____3631
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3687 =
            let uu____3688 =
              let uu____3715 = star_type' env e in
              let uu____3716 =
                let uu____3731 =
                  let uu____3738 = star_type' env t2 in
                  FStar_Util.Inl uu____3738 in
                (uu____3731, FStar_Pervasives_Native.None) in
              (uu____3715, uu____3716, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3688 in
          mk1 uu____3687
      | FStar_Syntax_Syntax.Tm_ascribed uu____3769 ->
          let uu____3796 =
            let uu____3797 =
              let uu____3798 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____3798 in
            FStar_Errors.Err uu____3797 in
          FStar_Exn.raise uu____3796
      | FStar_Syntax_Syntax.Tm_refine uu____3799 ->
          let uu____3806 =
            let uu____3807 =
              let uu____3808 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3808 in
            FStar_Errors.Err uu____3807 in
          FStar_Exn.raise uu____3806
      | FStar_Syntax_Syntax.Tm_uinst uu____3809 ->
          let uu____3816 =
            let uu____3817 =
              let uu____3818 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3818 in
            FStar_Errors.Err uu____3817 in
          FStar_Exn.raise uu____3816
      | FStar_Syntax_Syntax.Tm_constant uu____3819 ->
          let uu____3820 =
            let uu____3821 =
              let uu____3822 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3822 in
            FStar_Errors.Err uu____3821 in
          FStar_Exn.raise uu____3820
      | FStar_Syntax_Syntax.Tm_match uu____3823 ->
          let uu____3846 =
            let uu____3847 =
              let uu____3848 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3848 in
            FStar_Errors.Err uu____3847 in
          FStar_Exn.raise uu____3846
      | FStar_Syntax_Syntax.Tm_let uu____3849 ->
          let uu____3862 =
            let uu____3863 =
              let uu____3864 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____3864 in
            FStar_Errors.Err uu____3863 in
          FStar_Exn.raise uu____3862
      | FStar_Syntax_Syntax.Tm_uvar uu____3865 ->
          let uu____3882 =
            let uu____3883 =
              let uu____3884 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____3884 in
            FStar_Errors.Err uu____3883 in
          FStar_Exn.raise uu____3882
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____3885 =
            let uu____3886 =
              let uu____3887 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____3887 in
            FStar_Errors.Err uu____3886 in
          FStar_Exn.raise uu____3885
      | FStar_Syntax_Syntax.Tm_delayed uu____3888 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___342_3917  ->
    match uu___342_3917 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___341_3924  ->
                match uu___341_3924 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3925 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3929 =
      let uu____3930 = FStar_Syntax_Subst.compress t in
      uu____3930.FStar_Syntax_Syntax.n in
    match uu____3929 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3956 =
            let uu____3957 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____3957 in
          is_C uu____3956 in
        if r
        then
          ((let uu____3973 =
              let uu____3974 =
                FStar_List.for_all
                  (fun uu____3982  ->
                     match uu____3982 with | (h,uu____3988) -> is_C h) args in
              Prims.op_Negation uu____3974 in
            if uu____3973 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3992 =
              let uu____3993 =
                FStar_List.for_all
                  (fun uu____4002  ->
                     match uu____4002 with
                     | (h,uu____4008) ->
                         let uu____4009 = is_C h in
                         Prims.op_Negation uu____4009) args in
              Prims.op_Negation uu____3993 in
            if uu____3992 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4029 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4029 with
         | M t1 ->
             ((let uu____4032 = is_C t1 in
               if uu____4032 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4036) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4042) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4048,uu____4049) -> is_C t1
    | uu____4090 -> false
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
          let uu____4113 =
            let uu____4114 =
              let uu____4129 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4130 =
                let uu____4137 =
                  let uu____4142 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4142) in
                [uu____4137] in
              (uu____4129, uu____4130) in
            FStar_Syntax_Syntax.Tm_app uu____4114 in
          mk1 uu____4113 in
        let uu____4157 =
          let uu____4158 = FStar_Syntax_Syntax.mk_binder p in [uu____4158] in
        FStar_Syntax_Util.abs uu____4157 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___343_4161  ->
    match uu___343_4161 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4162 -> false
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
        let return_if uu____4337 =
          match uu____4337 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4364 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4366 =
                       let uu____4367 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4367 in
                     Prims.op_Negation uu____4366) in
                if uu____4364
                then
                  let uu____4368 =
                    let uu____4369 =
                      let uu____4370 = FStar_Syntax_Print.term_to_string e in
                      let uu____4371 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4372 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4370 uu____4371 uu____4372 in
                    FStar_Errors.Err uu____4369 in
                  FStar_Exn.raise uu____4368
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4389 = mk_return env t1 s_e in
                     ((M t1), uu____4389, u_e)))
               | (M t1,N t2) ->
                   let uu____4392 =
                     let uu____4393 =
                       let uu____4394 = FStar_Syntax_Print.term_to_string e in
                       let uu____4395 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4396 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4394 uu____4395 uu____4396 in
                     FStar_Errors.Err uu____4393 in
                   FStar_Exn.raise uu____4392) in
        let ensure_m env1 e2 =
          let strip_m uu___344_4437 =
            match uu___344_4437 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4453 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4473 =
                let uu____4474 =
                  let uu____4479 =
                    let uu____4480 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____4480 in
                  (uu____4479, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____4474 in
              FStar_Exn.raise uu____4473
          | M uu____4487 ->
              let uu____4488 = check env1 e2 context_nm in strip_m uu____4488 in
        let uu____4495 =
          let uu____4496 = FStar_Syntax_Subst.compress e in
          uu____4496.FStar_Syntax_Syntax.n in
        match uu____4495 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4505 ->
            let uu____4506 = infer env e in return_if uu____4506
        | FStar_Syntax_Syntax.Tm_name uu____4513 ->
            let uu____4514 = infer env e in return_if uu____4514
        | FStar_Syntax_Syntax.Tm_fvar uu____4521 ->
            let uu____4522 = infer env e in return_if uu____4522
        | FStar_Syntax_Syntax.Tm_abs uu____4529 ->
            let uu____4546 = infer env e in return_if uu____4546
        | FStar_Syntax_Syntax.Tm_constant uu____4553 ->
            let uu____4554 = infer env e in return_if uu____4554
        | FStar_Syntax_Syntax.Tm_app uu____4561 ->
            let uu____4576 = infer env e in return_if uu____4576
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4644) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4650) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4656,uu____4657) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4698 ->
            let uu____4711 =
              let uu____4712 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4712 in
            failwith uu____4711
        | FStar_Syntax_Syntax.Tm_type uu____4719 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4726 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4745 ->
            let uu____4752 =
              let uu____4753 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4753 in
            failwith uu____4752
        | FStar_Syntax_Syntax.Tm_uvar uu____4760 ->
            let uu____4777 =
              let uu____4778 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4778 in
            failwith uu____4777
        | FStar_Syntax_Syntax.Tm_delayed uu____4785 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4816 =
              let uu____4817 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4817 in
            failwith uu____4816
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
      let uu____4841 =
        let uu____4842 = FStar_Syntax_Subst.compress e in
        uu____4842.FStar_Syntax_Syntax.n in
      match uu____4841 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____4901;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____4902;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____4908 =
                  let uu___359_4909 = rc in
                  let uu____4910 =
                    let uu____4915 =
                      let uu____4916 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____4916 in
                    FStar_Pervasives_Native.Some uu____4915 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___359_4909.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____4910;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___359_4909.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____4908 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___360_4926 = env in
            let uu____4927 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____4927;
              subst = (uu___360_4926.subst);
              tc_const = (uu___360_4926.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____4947  ->
                 match uu____4947 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___361_4960 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___361_4960.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___361_4960.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____4961 =
            FStar_List.fold_left
              (fun uu____4990  ->
                 fun uu____4991  ->
                   match (uu____4990, uu____4991) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5039 = is_C c in
                       if uu____5039
                       then
                         let xw =
                           let uu____5047 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5047 in
                         let x =
                           let uu___362_5049 = bv in
                           let uu____5050 =
                             let uu____5053 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5053 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___362_5049.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___362_5049.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5050
                           } in
                         let env3 =
                           let uu___363_5055 = env2 in
                           let uu____5056 =
                             let uu____5059 =
                               let uu____5060 =
                                 let uu____5067 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5067) in
                               FStar_Syntax_Syntax.NT uu____5060 in
                             uu____5059 :: (env2.subst) in
                           {
                             env = (uu___363_5055.env);
                             subst = uu____5056;
                             tc_const = (uu___363_5055.tc_const)
                           } in
                         let uu____5068 =
                           let uu____5071 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5072 =
                             let uu____5075 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5075 :: acc in
                           uu____5071 :: uu____5072 in
                         (env3, uu____5068)
                       else
                         (let x =
                            let uu___364_5080 = bv in
                            let uu____5081 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___364_5080.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___364_5080.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5081
                            } in
                          let uu____5084 =
                            let uu____5087 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5087 :: acc in
                          (env2, uu____5084))) (env1, []) binders1 in
          (match uu____4961 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5107 =
                 let check_what =
                   let uu____5125 = is_monadic rc_opt1 in
                   if uu____5125 then check_m else check_n in
                 let uu____5137 = check_what env2 body1 in
                 match uu____5137 with
                 | (t,s_body,u_body) ->
                     let uu____5153 =
                       let uu____5154 =
                         let uu____5155 = is_monadic rc_opt1 in
                         if uu____5155 then M t else N t in
                       comp_of_nm uu____5154 in
                     (uu____5153, s_body, u_body) in
               (match uu____5107 with
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
                                 let uu____5180 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___345_5184  ->
                                           match uu___345_5184 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5185 -> false)) in
                                 if uu____5180
                                 then
                                   let uu____5186 =
                                     FStar_List.filter
                                       (fun uu___346_5190  ->
                                          match uu___346_5190 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5191 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5186
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5200 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___347_5204  ->
                                         match uu___347_5204 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5205 -> false)) in
                               if uu____5200
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___348_5212  ->
                                        match uu___348_5212 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5213 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5214 =
                                   let uu____5215 =
                                     let uu____5220 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5220 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5215 flags in
                                 FStar_Pervasives_Native.Some uu____5214
                               else
                                 (let uu____5222 =
                                    let uu___365_5223 = rc in
                                    let uu____5224 =
                                      let uu____5229 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5229 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___365_5223.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5224;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___365_5223.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5222)) in
                    let uu____5230 =
                      let comp1 =
                        let uu____5240 = is_monadic rc_opt1 in
                        let uu____5241 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5240 uu____5241 in
                      let uu____5242 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5242,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5230 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5284 =
                             let uu____5285 =
                               let uu____5302 =
                                 let uu____5305 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5305 s_rc_opt in
                               (s_binders1, s_body1, uu____5302) in
                             FStar_Syntax_Syntax.Tm_abs uu____5285 in
                           mk1 uu____5284 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5315 =
                             let uu____5316 =
                               let uu____5333 =
                                 let uu____5336 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5336 u_rc_opt in
                               (u_binders2, u_body2, uu____5333) in
                             FStar_Syntax_Syntax.Tm_abs uu____5316 in
                           mk1 uu____5315 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5346;_};
            FStar_Syntax_Syntax.fv_delta = uu____5347;
            FStar_Syntax_Syntax.fv_qual = uu____5348;_}
          ->
          let uu____5351 =
            let uu____5356 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5356 in
          (match uu____5351 with
           | (uu____5387,t) ->
               let uu____5389 = let uu____5390 = normalize1 t in N uu____5390 in
               (uu____5389, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5391;
             FStar_Syntax_Syntax.vars = uu____5392;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5455 = FStar_Syntax_Util.head_and_args e in
          (match uu____5455 with
           | (unary_op,uu____5477) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5536;
             FStar_Syntax_Syntax.vars = uu____5537;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5613 = FStar_Syntax_Util.head_and_args e in
          (match uu____5613 with
           | (unary_op,uu____5635) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5700;
             FStar_Syntax_Syntax.vars = uu____5701;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____5739 = infer env a in
          (match uu____5739 with
           | (t,s,u) ->
               let uu____5755 = FStar_Syntax_Util.head_and_args e in
               (match uu____5755 with
                | (head1,uu____5777) ->
                    let uu____5798 =
                      let uu____5799 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____5799 in
                    let uu____5800 =
                      let uu____5803 =
                        let uu____5804 =
                          let uu____5819 =
                            let uu____5822 = FStar_Syntax_Syntax.as_arg s in
                            [uu____5822] in
                          (head1, uu____5819) in
                        FStar_Syntax_Syntax.Tm_app uu____5804 in
                      mk1 uu____5803 in
                    let uu____5827 =
                      let uu____5830 =
                        let uu____5831 =
                          let uu____5846 =
                            let uu____5849 = FStar_Syntax_Syntax.as_arg u in
                            [uu____5849] in
                          (head1, uu____5846) in
                        FStar_Syntax_Syntax.Tm_app uu____5831 in
                      mk1 uu____5830 in
                    (uu____5798, uu____5800, uu____5827)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5858;
             FStar_Syntax_Syntax.vars = uu____5859;_},(a1,uu____5861)::a2::[])
          ->
          let uu____5903 = infer env a1 in
          (match uu____5903 with
           | (t,s,u) ->
               let uu____5919 = FStar_Syntax_Util.head_and_args e in
               (match uu____5919 with
                | (head1,uu____5941) ->
                    let uu____5962 =
                      let uu____5965 =
                        let uu____5966 =
                          let uu____5981 =
                            let uu____5984 = FStar_Syntax_Syntax.as_arg s in
                            [uu____5984; a2] in
                          (head1, uu____5981) in
                        FStar_Syntax_Syntax.Tm_app uu____5966 in
                      mk1 uu____5965 in
                    let uu____6001 =
                      let uu____6004 =
                        let uu____6005 =
                          let uu____6020 =
                            let uu____6023 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6023; a2] in
                          (head1, uu____6020) in
                        FStar_Syntax_Syntax.Tm_app uu____6005 in
                      mk1 uu____6004 in
                    (t, uu____5962, uu____6001)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6044;
             FStar_Syntax_Syntax.vars = uu____6045;_},uu____6046)
          ->
          let uu____6067 =
            let uu____6068 =
              let uu____6073 =
                let uu____6074 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6074 in
              (uu____6073, (e.FStar_Syntax_Syntax.pos)) in
            FStar_Errors.Error uu____6068 in
          FStar_Exn.raise uu____6067
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6081;
             FStar_Syntax_Syntax.vars = uu____6082;_},uu____6083)
          ->
          let uu____6104 =
            let uu____6105 =
              let uu____6110 =
                let uu____6111 = FStar_Syntax_Print.term_to_string e in
                FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6111 in
              (uu____6110, (e.FStar_Syntax_Syntax.pos)) in
            FStar_Errors.Error uu____6105 in
          FStar_Exn.raise uu____6104
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6140 = check_n env head1 in
          (match uu____6140 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6160 =
                   let uu____6161 = FStar_Syntax_Subst.compress t in
                   uu____6161.FStar_Syntax_Syntax.n in
                 match uu____6160 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6164 -> true
                 | uu____6177 -> false in
               let rec flatten1 t =
                 let uu____6194 =
                   let uu____6195 = FStar_Syntax_Subst.compress t in
                   uu____6195.FStar_Syntax_Syntax.n in
                 match uu____6194 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6212);
                                FStar_Syntax_Syntax.pos = uu____6213;
                                FStar_Syntax_Syntax.vars = uu____6214;_})
                     when is_arrow t1 ->
                     let uu____6239 = flatten1 t1 in
                     (match uu____6239 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6321,uu____6322)
                     -> flatten1 e1
                 | uu____6363 ->
                     let uu____6364 =
                       let uu____6365 =
                         let uu____6366 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6366 in
                       FStar_Errors.Err uu____6365 in
                     FStar_Exn.raise uu____6364 in
               let uu____6379 = flatten1 t_head in
               (match uu____6379 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6439 =
                          let uu____6440 =
                            let uu____6441 = FStar_Util.string_of_int n1 in
                            let uu____6448 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____6459 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6441 uu____6448 uu____6459 in
                          FStar_Errors.Err uu____6440 in
                        FStar_Exn.raise uu____6439)
                     else ();
                     (let uu____6467 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____6467 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6508 args1 =
                            match uu____6508 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6582 =
                                       let uu____6583 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____6583.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____6582
                                 | (binders3,[]) ->
                                     let uu____6613 =
                                       let uu____6614 =
                                         let uu____6617 =
                                           let uu____6618 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6618 in
                                         FStar_Syntax_Subst.compress
                                           uu____6617 in
                                       uu____6614.FStar_Syntax_Syntax.n in
                                     (match uu____6613 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6643 =
                                            let uu____6644 =
                                              let uu____6645 =
                                                let uu____6658 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____6658) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6645 in
                                            mk1 uu____6644 in
                                          N uu____6643
                                      | uu____6665 -> failwith "wat?")
                                 | ([],uu____6666::uu____6667) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6707)::binders3,(arg,uu____6710)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____6763 = FStar_List.splitAt n' binders1 in
                          (match uu____6763 with
                           | (binders2,uu____6795) ->
                               let uu____6820 =
                                 let uu____6839 =
                                   FStar_List.map2
                                     (fun uu____6887  ->
                                        fun uu____6888  ->
                                          match (uu____6887, uu____6888) with
                                          | ((bv,uu____6920),(arg,q)) ->
                                              let uu____6931 =
                                                let uu____6932 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____6932.FStar_Syntax_Syntax.n in
                                              (match uu____6931 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____6949 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____6973 ->
                                                   let uu____6974 =
                                                     check_n env arg in
                                                   (match uu____6974 with
                                                    | (uu____6995,s_arg,u_arg)
                                                        ->
                                                        let uu____6998 =
                                                          let uu____7005 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7005
                                                          then
                                                            let uu____7012 =
                                                              let uu____7017
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7017, q) in
                                                            [uu____7012;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____6998))))
                                     binders2 args in
                                 FStar_List.split uu____6839 in
                               (match uu____6820 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7106 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7115 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7106, uu____7115)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7181) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7187) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7193,uu____7194) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7236 = let uu____7237 = env.tc_const c in N uu____7237 in
          (uu____7236, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7238 ->
          let uu____7251 =
            let uu____7252 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7252 in
          failwith uu____7251
      | FStar_Syntax_Syntax.Tm_type uu____7259 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7266 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7285 ->
          let uu____7292 =
            let uu____7293 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7293 in
          failwith uu____7292
      | FStar_Syntax_Syntax.Tm_uvar uu____7300 ->
          let uu____7317 =
            let uu____7318 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7318 in
          failwith uu____7317
      | FStar_Syntax_Syntax.Tm_delayed uu____7325 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7356 =
            let uu____7357 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7357 in
          failwith uu____7356
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
          let uu____7402 = check_n env e0 in
          match uu____7402 with
          | (uu____7415,s_e0,u_e0) ->
              let uu____7418 =
                let uu____7447 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7508 = FStar_Syntax_Subst.open_branch b in
                       match uu____7508 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___366_7550 = env in
                             let uu____7551 =
                               let uu____7552 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7552 in
                             {
                               env = uu____7551;
                               subst = (uu___366_7550.subst);
                               tc_const = (uu___366_7550.tc_const)
                             } in
                           let uu____7555 = f env1 body in
                           (match uu____7555 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7627 ->
                           FStar_Exn.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____7447 in
              (match uu____7418 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7729 = FStar_List.hd nms in
                     match uu____7729 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___349_7735  ->
                          match uu___349_7735 with
                          | M uu____7736 -> true
                          | uu____7737 -> false) nms in
                   let uu____7738 =
                     let uu____7775 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____7865  ->
                              match uu____7865 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8042 =
                                         check env original_body (M t2) in
                                       (match uu____8042 with
                                        | (uu____8079,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8118,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____7775 in
                   (match uu____7738 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8302  ->
                                 match uu____8302 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8353 =
                                         let uu____8354 =
                                           let uu____8369 =
                                             let uu____8376 =
                                               let uu____8381 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____8382 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____8381, uu____8382) in
                                             [uu____8376] in
                                           (s_body, uu____8369) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8354 in
                                       mk1 uu____8353 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____8414 =
                              let uu____8415 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8415] in
                            let uu____8416 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____8414 uu____8416
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____8422 =
                              let uu____8429 =
                                let uu____8430 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8430 in
                              [uu____8429] in
                            let uu____8431 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____8422 uu____8431 in
                          let uu____8434 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____8473 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____8434, uu____8473)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____8490 =
                             let uu____8493 =
                               let uu____8494 =
                                 let uu____8521 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____8521,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8494 in
                             mk1 uu____8493 in
                           let uu____8558 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____8490, uu____8558))))
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
              let uu____8605 = FStar_Syntax_Syntax.mk_binder x in
              [uu____8605] in
            let uu____8606 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____8606 with
            | (x_binders1,e21) ->
                let uu____8619 = infer env e1 in
                (match uu____8619 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____8636 = is_C t1 in
                       if uu____8636
                       then
                         let uu___367_8637 = binding in
                         let uu____8638 =
                           let uu____8641 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____8641 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___367_8637.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___367_8637.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____8638;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___367_8637.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___367_8637.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___368_8644 = env in
                       let uu____8645 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___369_8647 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___369_8647.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___369_8647.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8645;
                         subst = (uu___368_8644.subst);
                         tc_const = (uu___368_8644.tc_const)
                       } in
                     let uu____8648 = proceed env1 e21 in
                     (match uu____8648 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___370_8665 = binding in
                            let uu____8666 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___370_8665.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___370_8665.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____8666;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___370_8665.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___370_8665.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____8669 =
                            let uu____8672 =
                              let uu____8673 =
                                let uu____8686 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___371_8696 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___371_8696.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___371_8696.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___371_8696.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___371_8696.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____8686) in
                              FStar_Syntax_Syntax.Tm_let uu____8673 in
                            mk1 uu____8672 in
                          let uu____8697 =
                            let uu____8700 =
                              let uu____8701 =
                                let uu____8714 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___372_8724 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___372_8724.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___372_8724.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___372_8724.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___372_8724.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8714) in
                              FStar_Syntax_Syntax.Tm_let uu____8701 in
                            mk1 uu____8700 in
                          (nm_rec, uu____8669, uu____8697))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___373_8733 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___373_8733.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___373_8733.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___373_8733.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___374_8735 = env in
                       let uu____8736 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___375_8738 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___375_8738.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___375_8738.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8736;
                         subst = (uu___374_8735.subst);
                         tc_const = (uu___374_8735.tc_const)
                       } in
                     let uu____8739 = ensure_m env1 e21 in
                     (match uu____8739 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____8762 =
                              let uu____8763 =
                                let uu____8778 =
                                  let uu____8785 =
                                    let uu____8790 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____8791 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8790, uu____8791) in
                                  [uu____8785] in
                                (s_e2, uu____8778) in
                              FStar_Syntax_Syntax.Tm_app uu____8763 in
                            mk1 uu____8762 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____8810 =
                              let uu____8811 =
                                let uu____8826 =
                                  let uu____8833 =
                                    let uu____8838 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____8838) in
                                  [uu____8833] in
                                (s_e1, uu____8826) in
                              FStar_Syntax_Syntax.Tm_app uu____8811 in
                            mk1 uu____8810 in
                          let uu____8853 =
                            let uu____8854 =
                              let uu____8855 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8855] in
                            FStar_Syntax_Util.abs uu____8854 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____8856 =
                            let uu____8859 =
                              let uu____8860 =
                                let uu____8873 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___376_8883 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___376_8883.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___376_8883.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___376_8883.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___376_8883.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8873) in
                              FStar_Syntax_Syntax.Tm_let uu____8860 in
                            mk1 uu____8859 in
                          ((M t2), uu____8853, uu____8856)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8895 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____8895 in
      let uu____8896 = check env e mn in
      match uu____8896 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8912 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8934 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____8934 in
      let uu____8935 = check env e mn in
      match uu____8935 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8951 -> failwith "[check_m]: impossible"
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
        (let uu____8981 =
           let uu____8982 = is_C c in Prims.op_Negation uu____8982 in
         if uu____8981 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____8990 =
           let uu____8991 = FStar_Syntax_Subst.compress c in
           uu____8991.FStar_Syntax_Syntax.n in
         match uu____8990 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9016 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9016 with
              | (wp_head,wp_args) ->
                  ((let uu____9054 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9068 =
                           let uu____9069 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9069 in
                         Prims.op_Negation uu____9068) in
                    if uu____9054 then failwith "mismatch" else ());
                   (let uu____9077 =
                      let uu____9078 =
                        let uu____9093 =
                          FStar_List.map2
                            (fun uu____9121  ->
                               fun uu____9122  ->
                                 match (uu____9121, uu____9122) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9159 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9159
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9162 = print_implicit q in
                                         let uu____9163 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b\n"
                                           uu____9162 uu____9163)
                                      else ();
                                      (let uu____9165 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9165, q)))) args wp_args in
                        (head1, uu____9093) in
                      FStar_Syntax_Syntax.Tm_app uu____9078 in
                    mk1 uu____9077)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9199 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9199 with
              | (binders_orig,comp1) ->
                  let uu____9206 =
                    let uu____9221 =
                      FStar_List.map
                        (fun uu____9255  ->
                           match uu____9255 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9275 = is_C h in
                               if uu____9275
                               then
                                 let w' =
                                   let uu____9287 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9287 in
                                 let uu____9288 =
                                   let uu____9295 =
                                     let uu____9302 =
                                       let uu____9307 =
                                         let uu____9308 =
                                           let uu____9309 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____9309 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9308 in
                                       (uu____9307, q) in
                                     [uu____9302] in
                                   (w', q) :: uu____9295 in
                                 (w', uu____9288)
                               else
                                 (let x =
                                    let uu____9330 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9330 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9221 in
                  (match uu____9206 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____9385 =
                           let uu____9388 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9388 in
                         FStar_Syntax_Subst.subst_comp uu____9385 comp1 in
                       let app =
                         let uu____9392 =
                           let uu____9393 =
                             let uu____9408 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9423 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____9424 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9423, uu____9424)) bvs in
                             (wp, uu____9408) in
                           FStar_Syntax_Syntax.Tm_app uu____9393 in
                         mk1 uu____9392 in
                       let comp3 =
                         let uu____9432 = type_of_comp comp2 in
                         let uu____9433 = is_monadic_comp comp2 in
                         trans_G env uu____9432 uu____9433 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9435,uu____9436) ->
             trans_F_ env e wp
         | uu____9477 -> failwith "impossible trans_F_")
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
            let uu____9482 =
              let uu____9483 = star_type' env h in
              let uu____9486 =
                let uu____9495 =
                  let uu____9500 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____9500) in
                [uu____9495] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9483;
                FStar_Syntax_Syntax.effect_args = uu____9486;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____9482
          else
            (let uu____9510 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____9510)
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
    fun t  -> let uu____9521 = n env.env t in star_type' env uu____9521
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____9536 = n env.env t in check_n env uu____9536
let trans_F:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9546 = n env.env c in
        let uu____9547 = n env.env wp in trans_F_ env uu____9546 uu____9547