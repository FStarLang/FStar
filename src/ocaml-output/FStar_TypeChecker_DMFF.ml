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
              let uu___290_93 = a in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___290_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___290_93.FStar_Syntax_Syntax.index);
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
                          let uu___291_2059 = t1 in
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
                              (uu___291_2059.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___291_2059.FStar_Syntax_Syntax.vars)
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
                      let uu___292_2794 = ed in
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
                          (uu___292_2794.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___292_2794.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___292_2794.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___292_2794.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___292_2794.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___292_2794.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___292_2794.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2795;
                        FStar_Syntax_Syntax.ite_wp = uu____2799;
                        FStar_Syntax_Syntax.stronger = uu____2803;
                        FStar_Syntax_Syntax.close_wp = uu____2807;
                        FStar_Syntax_Syntax.assert_p = uu____2811;
                        FStar_Syntax_Syntax.assume_p = uu____2815;
                        FStar_Syntax_Syntax.null_wp = uu____2819;
                        FStar_Syntax_Syntax.trivial = uu____2823;
                        FStar_Syntax_Syntax.repr =
                          (uu___292_2794.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___292_2794.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___292_2794.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___292_2794.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2723, uu____2793)))))
type env_ = env[@@deriving show]
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___293_2838 = dmff_env in
      {
        env = env';
        subst = (uu___293_2838.subst);
        tc_const = (uu___293_2838.tc_const)
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
  fun uu___279_2873  ->
    match uu___279_2873 with
    | FStar_Syntax_Syntax.Total (t,uu____2875) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___278_2888  ->
                match uu___278_2888 with
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
  fun uu___280_2905  ->
    match uu___280_2905 with
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
                       let uu___294_3118 = bv in
                       let uu____3119 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___294_3118.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___294_3118.FStar_Syntax_Syntax.index);
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
               let uu____3570 =
                 let uu____3571 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3571 in
               (FStar_Errors.WrongTerm, uu____3570) in
             FStar_Errors.raise_err uu____3565)
      | FStar_Syntax_Syntax.Tm_bvar uu____3572 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3573 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3574 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3575 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3599 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3599 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___297_3607 = env in
                 let uu____3608 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3608;
                   subst = (uu___297_3607.subst);
                   tc_const = (uu___297_3607.tc_const)
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
               ((let uu___298_3628 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___298_3628.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___298_3628.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3635 =
            let uu____3636 =
              let uu____3643 = star_type' env t2 in (uu____3643, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3636 in
          mk1 uu____3635
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3691 =
            let uu____3692 =
              let uu____3719 = star_type' env e in
              let uu____3720 =
                let uu____3735 =
                  let uu____3742 = star_type' env t2 in
                  FStar_Util.Inl uu____3742 in
                (uu____3735, FStar_Pervasives_Native.None) in
              (uu____3719, uu____3720, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3692 in
          mk1 uu____3691
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3820 =
            let uu____3821 =
              let uu____3848 = star_type' env e in
              let uu____3849 =
                let uu____3864 =
                  let uu____3871 =
                    star_type' env (FStar_Syntax_Util.comp_result c) in
                  FStar_Util.Inl uu____3871 in
                (uu____3864, FStar_Pervasives_Native.None) in
              (uu____3848, uu____3849, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3821 in
          mk1 uu____3820
      | FStar_Syntax_Syntax.Tm_refine uu____3902 ->
          let uu____3909 =
            let uu____3914 =
              let uu____3915 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3915 in
            (FStar_Errors.TermOutsideOfDefLanguage, uu____3914) in
          FStar_Errors.raise_err uu____3909
      | FStar_Syntax_Syntax.Tm_uinst uu____3916 ->
          let uu____3923 =
            let uu____3928 =
              let uu____3929 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3929 in
            (FStar_Errors.TermOutsideOfDefLanguage, uu____3928) in
          FStar_Errors.raise_err uu____3923
      | FStar_Syntax_Syntax.Tm_constant uu____3930 ->
          let uu____3931 =
            let uu____3936 =
              let uu____3937 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3937 in
            (FStar_Errors.TermOutsideOfDefLanguage, uu____3936) in
          FStar_Errors.raise_err uu____3931
      | FStar_Syntax_Syntax.Tm_match uu____3938 ->
          let uu____3961 =
            let uu____3966 =
              let uu____3967 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3967 in
            (FStar_Errors.TermOutsideOfDefLanguage, uu____3966) in
          FStar_Errors.raise_err uu____3961
      | FStar_Syntax_Syntax.Tm_let uu____3968 ->
          let uu____3981 =
            let uu____3986 =
              let uu____3987 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____3987 in
            (FStar_Errors.TermOutsideOfDefLanguage, uu____3986) in
          FStar_Errors.raise_err uu____3981
      | FStar_Syntax_Syntax.Tm_uvar uu____3988 ->
          let uu____4005 =
            let uu____4010 =
              let uu____4011 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4011 in
            (FStar_Errors.TermOutsideOfDefLanguage, uu____4010) in
          FStar_Errors.raise_err uu____4005
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4012 =
            let uu____4017 =
              let uu____4018 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4018 in
            (FStar_Errors.TermOutsideOfDefLanguage, uu____4017) in
          FStar_Errors.raise_err uu____4012
      | FStar_Syntax_Syntax.Tm_delayed uu____4019 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___282_4048  ->
    match uu___282_4048 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___281_4055  ->
                match uu___281_4055 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4056 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____4060 =
      let uu____4061 = FStar_Syntax_Subst.compress t in
      uu____4061.FStar_Syntax_Syntax.n in
    match uu____4060 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4087 =
            let uu____4088 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____4088 in
          is_C uu____4087 in
        if r
        then
          ((let uu____4104 =
              let uu____4105 =
                FStar_List.for_all
                  (fun uu____4113  ->
                     match uu____4113 with | (h,uu____4119) -> is_C h) args in
              Prims.op_Negation uu____4105 in
            if uu____4104 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4123 =
              let uu____4124 =
                FStar_List.for_all
                  (fun uu____4133  ->
                     match uu____4133 with
                     | (h,uu____4139) ->
                         let uu____4140 = is_C h in
                         Prims.op_Negation uu____4140) args in
              Prims.op_Negation uu____4124 in
            if uu____4123 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4160 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____4160 with
         | M t1 ->
             ((let uu____4163 = is_C t1 in
               if uu____4163 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4167) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4173) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4179,uu____4180) -> is_C t1
    | uu____4221 -> false
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
          let uu____4244 =
            let uu____4245 =
              let uu____4260 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4261 =
                let uu____4268 =
                  let uu____4273 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4273) in
                [uu____4268] in
              (uu____4260, uu____4261) in
            FStar_Syntax_Syntax.Tm_app uu____4245 in
          mk1 uu____4244 in
        let uu____4288 =
          let uu____4289 = FStar_Syntax_Syntax.mk_binder p in [uu____4289] in
        FStar_Syntax_Util.abs uu____4288 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___283_4292  ->
    match uu___283_4292 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4293 -> false
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
        let return_if uu____4468 =
          match uu____4468 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4495 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4497 =
                       let uu____4498 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4498 in
                     Prims.op_Negation uu____4497) in
                if uu____4495
                then
                  let uu____4499 =
                    let uu____4504 =
                      let uu____4505 = FStar_Syntax_Print.term_to_string e in
                      let uu____4506 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4507 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4505 uu____4506 uu____4507 in
                    (FStar_Errors.TypeMismatch, uu____4504) in
                  FStar_Errors.raise_err uu____4499
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4524 = mk_return env t1 s_e in
                     ((M t1), uu____4524, u_e)))
               | (M t1,N t2) ->
                   let uu____4527 =
                     let uu____4532 =
                       let uu____4533 = FStar_Syntax_Print.term_to_string e in
                       let uu____4534 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4535 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4533 uu____4534 uu____4535 in
                     (FStar_Errors.EffectfulAndPureComputationMismatch,
                       uu____4532) in
                   FStar_Errors.raise_err uu____4527) in
        let ensure_m env1 e2 =
          let strip_m uu___284_4576 =
            match uu___284_4576 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4592 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4612 =
                let uu____4617 =
                  let uu____4618 = FStar_Syntax_Print.term_to_string t in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4618 in
                (FStar_Errors.LetBoundMonadicMismatch, uu____4617) in
              FStar_Errors.raise_error uu____4612 e2.FStar_Syntax_Syntax.pos
          | M uu____4625 ->
              let uu____4626 = check env1 e2 context_nm in strip_m uu____4626 in
        let uu____4633 =
          let uu____4634 = FStar_Syntax_Subst.compress e in
          uu____4634.FStar_Syntax_Syntax.n in
        match uu____4633 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4643 ->
            let uu____4644 = infer env e in return_if uu____4644
        | FStar_Syntax_Syntax.Tm_name uu____4651 ->
            let uu____4652 = infer env e in return_if uu____4652
        | FStar_Syntax_Syntax.Tm_fvar uu____4659 ->
            let uu____4660 = infer env e in return_if uu____4660
        | FStar_Syntax_Syntax.Tm_abs uu____4667 ->
            let uu____4684 = infer env e in return_if uu____4684
        | FStar_Syntax_Syntax.Tm_constant uu____4691 ->
            let uu____4692 = infer env e in return_if uu____4692
        | FStar_Syntax_Syntax.Tm_app uu____4699 ->
            let uu____4714 = infer env e in return_if uu____4714
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4782) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4788) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4794,uu____4795) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4836 ->
            let uu____4849 =
              let uu____4850 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4850 in
            failwith uu____4849
        | FStar_Syntax_Syntax.Tm_type uu____4857 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4864 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4883 ->
            let uu____4890 =
              let uu____4891 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4891 in
            failwith uu____4890
        | FStar_Syntax_Syntax.Tm_uvar uu____4898 ->
            let uu____4915 =
              let uu____4916 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4916 in
            failwith uu____4915
        | FStar_Syntax_Syntax.Tm_delayed uu____4923 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4954 =
              let uu____4955 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4955 in
            failwith uu____4954
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
      let uu____4979 =
        let uu____4980 = FStar_Syntax_Subst.compress e in
        uu____4980.FStar_Syntax_Syntax.n in
      match uu____4979 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5039;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5040;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5046 =
                  let uu___299_5047 = rc in
                  let uu____5048 =
                    let uu____5053 =
                      let uu____5054 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____5054 in
                    FStar_Pervasives_Native.Some uu____5053 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___299_5047.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5048;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___299_5047.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____5046 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___300_5064 = env in
            let uu____5065 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____5065;
              subst = (uu___300_5064.subst);
              tc_const = (uu___300_5064.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____5085  ->
                 match uu____5085 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___301_5098 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___301_5098.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___301_5098.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____5099 =
            FStar_List.fold_left
              (fun uu____5128  ->
                 fun uu____5129  ->
                   match (uu____5128, uu____5129) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____5177 = is_C c in
                       if uu____5177
                       then
                         let xw =
                           let uu____5185 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5185 in
                         let x =
                           let uu___302_5187 = bv in
                           let uu____5188 =
                             let uu____5191 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____5191 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___302_5187.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___302_5187.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5188
                           } in
                         let env3 =
                           let uu___303_5193 = env2 in
                           let uu____5194 =
                             let uu____5197 =
                               let uu____5198 =
                                 let uu____5205 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5205) in
                               FStar_Syntax_Syntax.NT uu____5198 in
                             uu____5197 :: (env2.subst) in
                           {
                             env = (uu___303_5193.env);
                             subst = uu____5194;
                             tc_const = (uu___303_5193.tc_const)
                           } in
                         let uu____5206 =
                           let uu____5209 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5210 =
                             let uu____5213 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5213 :: acc in
                           uu____5209 :: uu____5210 in
                         (env3, uu____5206)
                       else
                         (let x =
                            let uu___304_5218 = bv in
                            let uu____5219 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___304_5218.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___304_5218.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5219
                            } in
                          let uu____5222 =
                            let uu____5225 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5225 :: acc in
                          (env2, uu____5222))) (env1, []) binders1 in
          (match uu____5099 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5245 =
                 let check_what =
                   let uu____5263 = is_monadic rc_opt1 in
                   if uu____5263 then check_m else check_n in
                 let uu____5275 = check_what env2 body1 in
                 match uu____5275 with
                 | (t,s_body,u_body) ->
                     let uu____5291 =
                       let uu____5292 =
                         let uu____5293 = is_monadic rc_opt1 in
                         if uu____5293 then M t else N t in
                       comp_of_nm uu____5292 in
                     (uu____5291, s_body, u_body) in
               (match uu____5245 with
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
                                 let uu____5318 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___285_5322  ->
                                           match uu___285_5322 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5323 -> false)) in
                                 if uu____5318
                                 then
                                   let uu____5324 =
                                     FStar_List.filter
                                       (fun uu___286_5328  ->
                                          match uu___286_5328 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5329 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5324
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5338 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___287_5342  ->
                                         match uu___287_5342 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5343 -> false)) in
                               if uu____5338
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___288_5350  ->
                                        match uu___288_5350 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5351 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5352 =
                                   let uu____5353 =
                                     let uu____5358 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5358 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5353 flags1 in
                                 FStar_Pervasives_Native.Some uu____5352
                               else
                                 (let uu____5360 =
                                    let uu___305_5361 = rc in
                                    let uu____5362 =
                                      let uu____5367 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5367 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___305_5361.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5362;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___305_5361.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5360)) in
                    let uu____5368 =
                      let comp1 =
                        let uu____5378 = is_monadic rc_opt1 in
                        let uu____5379 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5378 uu____5379 in
                      let uu____5380 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5380,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5368 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5422 =
                             let uu____5423 =
                               let uu____5440 =
                                 let uu____5443 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5443 s_rc_opt in
                               (s_binders1, s_body1, uu____5440) in
                             FStar_Syntax_Syntax.Tm_abs uu____5423 in
                           mk1 uu____5422 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5453 =
                             let uu____5454 =
                               let uu____5471 =
                                 let uu____5474 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5474 u_rc_opt in
                               (u_binders2, u_body2, uu____5471) in
                             FStar_Syntax_Syntax.Tm_abs uu____5454 in
                           mk1 uu____5453 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5484;_};
            FStar_Syntax_Syntax.fv_delta = uu____5485;
            FStar_Syntax_Syntax.fv_qual = uu____5486;_}
          ->
          let uu____5489 =
            let uu____5494 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5494 in
          (match uu____5489 with
           | (uu____5525,t) ->
               let uu____5527 = let uu____5528 = normalize1 t in N uu____5528 in
               (uu____5527, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5529;
             FStar_Syntax_Syntax.vars = uu____5530;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5593 = FStar_Syntax_Util.head_and_args e in
          (match uu____5593 with
           | (unary_op,uu____5615) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5674;
             FStar_Syntax_Syntax.vars = uu____5675;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest in
          let uu____5751 = FStar_Syntax_Util.head_and_args e in
          (match uu____5751 with
           | (unary_op,uu____5773) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1)) in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5838;
             FStar_Syntax_Syntax.vars = uu____5839;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____5877 = infer env a in
          (match uu____5877 with
           | (t,s,u) ->
               let uu____5893 = FStar_Syntax_Util.head_and_args e in
               (match uu____5893 with
                | (head1,uu____5915) ->
                    let uu____5936 =
                      let uu____5937 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu____5937 in
                    let uu____5938 =
                      let uu____5941 =
                        let uu____5942 =
                          let uu____5957 =
                            let uu____5960 = FStar_Syntax_Syntax.as_arg s in
                            [uu____5960] in
                          (head1, uu____5957) in
                        FStar_Syntax_Syntax.Tm_app uu____5942 in
                      mk1 uu____5941 in
                    let uu____5965 =
                      let uu____5968 =
                        let uu____5969 =
                          let uu____5984 =
                            let uu____5987 = FStar_Syntax_Syntax.as_arg u in
                            [uu____5987] in
                          (head1, uu____5984) in
                        FStar_Syntax_Syntax.Tm_app uu____5969 in
                      mk1 uu____5968 in
                    (uu____5936, uu____5938, uu____5965)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5996;
             FStar_Syntax_Syntax.vars = uu____5997;_},(a1,uu____5999)::a2::[])
          ->
          let uu____6041 = infer env a1 in
          (match uu____6041 with
           | (t,s,u) ->
               let uu____6057 = FStar_Syntax_Util.head_and_args e in
               (match uu____6057 with
                | (head1,uu____6079) ->
                    let uu____6100 =
                      let uu____6103 =
                        let uu____6104 =
                          let uu____6119 =
                            let uu____6122 = FStar_Syntax_Syntax.as_arg s in
                            [uu____6122; a2] in
                          (head1, uu____6119) in
                        FStar_Syntax_Syntax.Tm_app uu____6104 in
                      mk1 uu____6103 in
                    let uu____6139 =
                      let uu____6142 =
                        let uu____6143 =
                          let uu____6158 =
                            let uu____6161 = FStar_Syntax_Syntax.as_arg u in
                            [uu____6161; a2] in
                          (head1, uu____6158) in
                        FStar_Syntax_Syntax.Tm_app uu____6143 in
                      mk1 uu____6142 in
                    (t, uu____6100, uu____6139)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6182;
             FStar_Syntax_Syntax.vars = uu____6183;_},uu____6184)
          ->
          let uu____6205 =
            let uu____6210 =
              let uu____6211 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6211 in
            (FStar_Errors.IllAppliedConstant, uu____6210) in
          FStar_Errors.raise_error uu____6205 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6218;
             FStar_Syntax_Syntax.vars = uu____6219;_},uu____6220)
          ->
          let uu____6241 =
            let uu____6246 =
              let uu____6247 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6247 in
            (FStar_Errors.IllAppliedConstant, uu____6246) in
          FStar_Errors.raise_error uu____6241 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6276 = check_n env head1 in
          (match uu____6276 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6296 =
                   let uu____6297 = FStar_Syntax_Subst.compress t in
                   uu____6297.FStar_Syntax_Syntax.n in
                 match uu____6296 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6300 -> true
                 | uu____6313 -> false in
               let rec flatten1 t =
                 let uu____6330 =
                   let uu____6331 = FStar_Syntax_Subst.compress t in
                   uu____6331.FStar_Syntax_Syntax.n in
                 match uu____6330 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6348);
                                FStar_Syntax_Syntax.pos = uu____6349;
                                FStar_Syntax_Syntax.vars = uu____6350;_})
                     when is_arrow t1 ->
                     let uu____6375 = flatten1 t1 in
                     (match uu____6375 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6457,uu____6458)
                     -> flatten1 e1
                 | uu____6499 ->
                     let uu____6500 =
                       let uu____6505 =
                         let uu____6506 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6506 in
                       (FStar_Errors.NotFunctionType, uu____6505) in
                     FStar_Errors.raise_err uu____6500 in
               let uu____6519 = flatten1 t_head in
               (match uu____6519 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6579 =
                          let uu____6584 =
                            let uu____6585 = FStar_Util.string_of_int n1 in
                            let uu____6592 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____6603 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6585 uu____6592 uu____6603 in
                          (FStar_Errors.BinderAndArgsLengthMismatch,
                            uu____6584) in
                        FStar_Errors.raise_err uu____6579)
                     else ();
                     (let uu____6611 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____6611 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6652 args1 =
                            match uu____6652 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6726 =
                                       let uu____6727 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____6727.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____6726
                                 | (binders3,[]) ->
                                     let uu____6757 =
                                       let uu____6758 =
                                         let uu____6761 =
                                           let uu____6762 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6762 in
                                         FStar_Syntax_Subst.compress
                                           uu____6761 in
                                       uu____6758.FStar_Syntax_Syntax.n in
                                     (match uu____6757 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6787 =
                                            let uu____6788 =
                                              let uu____6789 =
                                                let uu____6802 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____6802) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6789 in
                                            mk1 uu____6788 in
                                          N uu____6787
                                      | uu____6809 -> failwith "wat?")
                                 | ([],uu____6810::uu____6811) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6851)::binders3,(arg,uu____6854)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____6907 = FStar_List.splitAt n' binders1 in
                          (match uu____6907 with
                           | (binders2,uu____6939) ->
                               let uu____6964 =
                                 let uu____6983 =
                                   FStar_List.map2
                                     (fun uu____7031  ->
                                        fun uu____7032  ->
                                          match (uu____7031, uu____7032) with
                                          | ((bv,uu____7064),(arg,q)) ->
                                              let uu____7075 =
                                                let uu____7076 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____7076.FStar_Syntax_Syntax.n in
                                              (match uu____7075 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7093 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____7117 ->
                                                   let uu____7118 =
                                                     check_n env arg in
                                                   (match uu____7118 with
                                                    | (uu____7139,s_arg,u_arg)
                                                        ->
                                                        let uu____7142 =
                                                          let uu____7149 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____7149
                                                          then
                                                            let uu____7156 =
                                                              let uu____7161
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____7161, q) in
                                                            [uu____7156;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____7142))))
                                     binders2 args in
                                 FStar_List.split uu____6983 in
                               (match uu____6964 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____7250 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____7259 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____7250, uu____7259)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7325) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7331) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7337,uu____7338) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7380 = let uu____7381 = env.tc_const c in N uu____7381 in
          (uu____7380, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7382 ->
          let uu____7395 =
            let uu____7396 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7396 in
          failwith uu____7395
      | FStar_Syntax_Syntax.Tm_type uu____7403 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7410 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7429 ->
          let uu____7436 =
            let uu____7437 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7437 in
          failwith uu____7436
      | FStar_Syntax_Syntax.Tm_uvar uu____7444 ->
          let uu____7461 =
            let uu____7462 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7462 in
          failwith uu____7461
      | FStar_Syntax_Syntax.Tm_delayed uu____7469 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7500 =
            let uu____7501 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7501 in
          failwith uu____7500
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
          let uu____7546 = check_n env e0 in
          match uu____7546 with
          | (uu____7559,s_e0,u_e0) ->
              let uu____7562 =
                let uu____7591 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7652 = FStar_Syntax_Subst.open_branch b in
                       match uu____7652 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___306_7694 = env in
                             let uu____7695 =
                               let uu____7696 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7696 in
                             {
                               env = uu____7695;
                               subst = (uu___306_7694.subst);
                               tc_const = (uu___306_7694.tc_const)
                             } in
                           let uu____7699 = f env1 body in
                           (match uu____7699 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7771 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____7591 in
              (match uu____7562 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7873 = FStar_List.hd nms in
                     match uu____7873 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___289_7879  ->
                          match uu___289_7879 with
                          | M uu____7880 -> true
                          | uu____7881 -> false) nms in
                   let uu____7882 =
                     let uu____7919 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8009  ->
                              match uu____8009 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8186 =
                                         check env original_body (M t2) in
                                       (match uu____8186 with
                                        | (uu____8223,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8262,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____7919 in
                   (match uu____7882 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____8446  ->
                                 match uu____8446 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8497 =
                                         let uu____8498 =
                                           let uu____8513 =
                                             let uu____8520 =
                                               let uu____8525 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____8526 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____8525, uu____8526) in
                                             [uu____8520] in
                                           (s_body, uu____8513) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8498 in
                                       mk1 uu____8497 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____8558 =
                              let uu____8559 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8559] in
                            let uu____8560 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____8558 uu____8560
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____8566 =
                              let uu____8573 =
                                let uu____8574 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8574 in
                              [uu____8573] in
                            let uu____8575 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____8566 uu____8575 in
                          let uu____8578 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____8617 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____8578, uu____8617)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____8634 =
                             let uu____8637 =
                               let uu____8638 =
                                 let uu____8665 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____8665,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8638 in
                             mk1 uu____8637 in
                           let uu____8702 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____8634, uu____8702))))
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
              let uu____8749 = FStar_Syntax_Syntax.mk_binder x in
              [uu____8749] in
            let uu____8750 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____8750 with
            | (x_binders1,e21) ->
                let uu____8763 = infer env e1 in
                (match uu____8763 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____8780 = is_C t1 in
                       if uu____8780
                       then
                         let uu___307_8781 = binding in
                         let uu____8782 =
                           let uu____8785 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____8785 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___307_8781.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___307_8781.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____8782;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___307_8781.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___307_8781.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___308_8788 = env in
                       let uu____8789 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___309_8791 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___309_8791.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___309_8791.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8789;
                         subst = (uu___308_8788.subst);
                         tc_const = (uu___308_8788.tc_const)
                       } in
                     let uu____8792 = proceed env1 e21 in
                     (match uu____8792 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___310_8809 = binding in
                            let uu____8810 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___310_8809.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___310_8809.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____8810;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___310_8809.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___310_8809.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____8813 =
                            let uu____8816 =
                              let uu____8817 =
                                let uu____8830 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___311_8840 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___311_8840.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___311_8840.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___311_8840.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___311_8840.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____8830) in
                              FStar_Syntax_Syntax.Tm_let uu____8817 in
                            mk1 uu____8816 in
                          let uu____8841 =
                            let uu____8844 =
                              let uu____8845 =
                                let uu____8858 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___312_8868 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___312_8868.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___312_8868.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___312_8868.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___312_8868.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8858) in
                              FStar_Syntax_Syntax.Tm_let uu____8845 in
                            mk1 uu____8844 in
                          (nm_rec, uu____8813, uu____8841))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___313_8877 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___313_8877.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___313_8877.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___313_8877.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___314_8879 = env in
                       let uu____8880 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___315_8882 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___315_8882.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___315_8882.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____8880;
                         subst = (uu___314_8879.subst);
                         tc_const = (uu___314_8879.tc_const)
                       } in
                     let uu____8883 = ensure_m env1 e21 in
                     (match uu____8883 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____8906 =
                              let uu____8907 =
                                let uu____8922 =
                                  let uu____8929 =
                                    let uu____8934 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____8935 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8934, uu____8935) in
                                  [uu____8929] in
                                (s_e2, uu____8922) in
                              FStar_Syntax_Syntax.Tm_app uu____8907 in
                            mk1 uu____8906 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____8954 =
                              let uu____8955 =
                                let uu____8970 =
                                  let uu____8977 =
                                    let uu____8982 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____8982) in
                                  [uu____8977] in
                                (s_e1, uu____8970) in
                              FStar_Syntax_Syntax.Tm_app uu____8955 in
                            mk1 uu____8954 in
                          let uu____8997 =
                            let uu____8998 =
                              let uu____8999 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8999] in
                            FStar_Syntax_Util.abs uu____8998 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____9000 =
                            let uu____9003 =
                              let uu____9004 =
                                let uu____9017 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___316_9027 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___316_9027.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___316_9027.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___316_9027.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___316_9027.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9017) in
                              FStar_Syntax_Syntax.Tm_let uu____9004 in
                            mk1 uu____9003 in
                          ((M t2), uu____8997, uu____9000)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9039 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____9039 in
      let uu____9040 = check env e mn in
      match uu____9040 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9056 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9078 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____9078 in
      let uu____9079 = check env e mn in
      match uu____9079 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9095 -> failwith "[check_m]: impossible"
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
        (let uu____9125 =
           let uu____9126 = is_C c in Prims.op_Negation uu____9126 in
         if uu____9125 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____9134 =
           let uu____9135 = FStar_Syntax_Subst.compress c in
           uu____9135.FStar_Syntax_Syntax.n in
         match uu____9134 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9160 = FStar_Syntax_Util.head_and_args wp in
             (match uu____9160 with
              | (wp_head,wp_args) ->
                  ((let uu____9198 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9212 =
                           let uu____9213 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9213 in
                         Prims.op_Negation uu____9212) in
                    if uu____9198 then failwith "mismatch" else ());
                   (let uu____9221 =
                      let uu____9222 =
                        let uu____9237 =
                          FStar_List.map2
                            (fun uu____9265  ->
                               fun uu____9266  ->
                                 match (uu____9265, uu____9266) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9303 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____9303
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____9306 = print_implicit q in
                                         let uu____9307 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b\n"
                                           uu____9306 uu____9307)
                                      else ();
                                      (let uu____9309 =
                                         trans_F_ env arg wp_arg in
                                       (uu____9309, q)))) args wp_args in
                        (head1, uu____9237) in
                      FStar_Syntax_Syntax.Tm_app uu____9222 in
                    mk1 uu____9221)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____9343 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____9343 with
              | (binders_orig,comp1) ->
                  let uu____9350 =
                    let uu____9365 =
                      FStar_List.map
                        (fun uu____9399  ->
                           match uu____9399 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____9419 = is_C h in
                               if uu____9419
                               then
                                 let w' =
                                   let uu____9431 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9431 in
                                 let uu____9432 =
                                   let uu____9439 =
                                     let uu____9446 =
                                       let uu____9451 =
                                         let uu____9452 =
                                           let uu____9453 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____9453 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9452 in
                                       (uu____9451, q) in
                                     [uu____9446] in
                                   (w', q) :: uu____9439 in
                                 (w', uu____9432)
                               else
                                 (let x =
                                    let uu____9474 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9474 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____9365 in
                  (match uu____9350 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____9529 =
                           let uu____9532 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9532 in
                         FStar_Syntax_Subst.subst_comp uu____9529 comp1 in
                       let app =
                         let uu____9536 =
                           let uu____9537 =
                             let uu____9552 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9567 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____9568 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____9567, uu____9568)) bvs in
                             (wp, uu____9552) in
                           FStar_Syntax_Syntax.Tm_app uu____9537 in
                         mk1 uu____9536 in
                       let comp3 =
                         let uu____9576 = type_of_comp comp2 in
                         let uu____9577 = is_monadic_comp comp2 in
                         trans_G env uu____9576 uu____9577 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9579,uu____9580) ->
             trans_F_ env e wp
         | uu____9621 -> failwith "impossible trans_F_")
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
            let uu____9626 =
              let uu____9627 = star_type' env h in
              let uu____9630 =
                let uu____9639 =
                  let uu____9644 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____9644) in
                [uu____9639] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9627;
                FStar_Syntax_Syntax.effect_args = uu____9630;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____9626
          else
            (let uu____9654 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____9654)
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
    fun t  -> let uu____9665 = n env.env t in star_type' env uu____9665
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____9680 = n env.env t in check_n env uu____9680
let trans_F:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9690 = n env.env c in
        let uu____9691 = n env.env wp in trans_F_ env uu____9690 uu____9691