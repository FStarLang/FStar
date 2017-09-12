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
              let uu___106_104 = a in
              let uu____105 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___106_104.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___106_104.FStar_Syntax_Syntax.index);
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
                  (fun uu____361  ->
                     match uu____361 with
                     | (t,b) ->
                         let uu____372 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____372)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____403 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____403)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____426 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____426) in
              let uu____427 =
                let uu____442 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____464 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____464 in
                    let uu____467 =
                      let uu____468 =
                        let uu____475 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____476 =
                          let uu____479 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____479] in
                        uu____475 :: uu____476 in
                      FStar_List.append binders uu____468 in
                    FStar_Syntax_Util.abs uu____467 body
                      FStar_Pervasives_Native.None in
                  let uu____484 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____485 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____484, uu____485) in
                match uu____442 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____519 =
                        let uu____520 =
                          let uu____535 =
                            let uu____542 =
                              FStar_List.map
                                (fun uu____562  ->
                                   match uu____562 with
                                   | (bv,uu____572) ->
                                       let uu____573 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____574 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____573, uu____574)) binders in
                            let uu____575 =
                              let uu____582 =
                                let uu____587 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____588 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____587, uu____588) in
                              let uu____589 =
                                let uu____596 =
                                  let uu____601 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____601) in
                                [uu____596] in
                              uu____582 :: uu____589 in
                            FStar_List.append uu____542 uu____575 in
                          (fv, uu____535) in
                        FStar_Syntax_Syntax.Tm_app uu____520 in
                      mk1 uu____519 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____427 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____660 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____660 in
                    let ret1 =
                      let uu____664 =
                        let uu____665 =
                          let uu____668 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____668 in
                        FStar_Syntax_Util.residual_tot uu____665 in
                      FStar_Pervasives_Native.Some uu____664 in
                    let body =
                      let uu____670 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____670 ret1 in
                    let uu____671 =
                      let uu____672 = mk_all_implicit binders in
                      let uu____679 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____672 uu____679 in
                    FStar_Syntax_Util.abs uu____671 body ret1 in
                  let c_pure1 =
                    let uu____707 = mk_lid "pure" in
                    register env1 uu____707 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____712 =
                        let uu____713 =
                          let uu____714 =
                            let uu____721 =
                              let uu____722 =
                                let uu____723 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____723 in
                              FStar_Syntax_Syntax.mk_binder uu____722 in
                            [uu____721] in
                          let uu____724 =
                            let uu____727 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____727 in
                          FStar_Syntax_Util.arrow uu____714 uu____724 in
                        mk_gctx uu____713 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____712 in
                    let r =
                      let uu____729 =
                        let uu____730 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____730 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____729 in
                    let ret1 =
                      let uu____734 =
                        let uu____735 =
                          let uu____738 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____738 in
                        FStar_Syntax_Util.residual_tot uu____735 in
                      FStar_Pervasives_Native.Some uu____734 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____746 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____749 =
                          let uu____758 =
                            let uu____761 =
                              let uu____762 =
                                let uu____763 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____763
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____762 in
                            [uu____761] in
                          FStar_List.append gamma_as_args uu____758 in
                        FStar_Syntax_Util.mk_app uu____746 uu____749 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____766 =
                      let uu____767 = mk_all_implicit binders in
                      let uu____774 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____767 uu____774 in
                    FStar_Syntax_Util.abs uu____766 outer_body ret1 in
                  let c_app1 =
                    let uu____810 = mk_lid "app" in
                    register env1 uu____810 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____817 =
                        let uu____824 =
                          let uu____825 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____825 in
                        [uu____824] in
                      let uu____826 =
                        let uu____829 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____829 in
                      FStar_Syntax_Util.arrow uu____817 uu____826 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____832 =
                        let uu____833 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____833 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____832 in
                    let ret1 =
                      let uu____837 =
                        let uu____838 =
                          let uu____841 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____841 in
                        FStar_Syntax_Util.residual_tot uu____838 in
                      FStar_Pervasives_Native.Some uu____837 in
                    let uu____842 =
                      let uu____843 = mk_all_implicit binders in
                      let uu____850 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____843 uu____850 in
                    let uu____885 =
                      let uu____886 =
                        let uu____895 =
                          let uu____898 =
                            let uu____901 =
                              let uu____910 =
                                let uu____913 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____913] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____910 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____901 in
                          let uu____914 =
                            let uu____919 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____919] in
                          uu____898 :: uu____914 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____895 in
                      FStar_Syntax_Util.mk_app c_app1 uu____886 in
                    FStar_Syntax_Util.abs uu____842 uu____885 ret1 in
                  let c_lift11 =
                    let uu____923 = mk_lid "lift1" in
                    register env1 uu____923 c_lift1 in
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
                      let uu____931 =
                        let uu____938 =
                          let uu____939 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____939 in
                        let uu____940 =
                          let uu____943 =
                            let uu____944 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____944 in
                          [uu____943] in
                        uu____938 :: uu____940 in
                      let uu____945 =
                        let uu____948 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____948 in
                      FStar_Syntax_Util.arrow uu____931 uu____945 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____951 =
                        let uu____952 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____952 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____951 in
                    let a2 =
                      let uu____954 =
                        let uu____955 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____955 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____954 in
                    let ret1 =
                      let uu____959 =
                        let uu____960 =
                          let uu____963 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____963 in
                        FStar_Syntax_Util.residual_tot uu____960 in
                      FStar_Pervasives_Native.Some uu____959 in
                    let uu____964 =
                      let uu____965 = mk_all_implicit binders in
                      let uu____972 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____965 uu____972 in
                    let uu____1015 =
                      let uu____1016 =
                        let uu____1025 =
                          let uu____1028 =
                            let uu____1031 =
                              let uu____1040 =
                                let uu____1043 =
                                  let uu____1046 =
                                    let uu____1055 =
                                      let uu____1058 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1058] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1055 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1046 in
                                let uu____1059 =
                                  let uu____1064 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1064] in
                                uu____1043 :: uu____1059 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1040 in
                            FStar_Syntax_Util.mk_app c_app1 uu____1031 in
                          let uu____1067 =
                            let uu____1072 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1072] in
                          uu____1028 :: uu____1067 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1025 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1016 in
                    FStar_Syntax_Util.abs uu____964 uu____1015 ret1 in
                  let c_lift21 =
                    let uu____1076 = mk_lid "lift2" in
                    register env1 uu____1076 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1083 =
                        let uu____1090 =
                          let uu____1091 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1091 in
                        [uu____1090] in
                      let uu____1092 =
                        let uu____1095 =
                          let uu____1096 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1096 in
                        FStar_Syntax_Syntax.mk_Total uu____1095 in
                      FStar_Syntax_Util.arrow uu____1083 uu____1092 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1101 =
                        let uu____1102 =
                          let uu____1105 =
                            let uu____1106 =
                              let uu____1113 =
                                let uu____1114 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1114 in
                              [uu____1113] in
                            let uu____1115 =
                              let uu____1118 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1118 in
                            FStar_Syntax_Util.arrow uu____1106 uu____1115 in
                          mk_ctx uu____1105 in
                        FStar_Syntax_Util.residual_tot uu____1102 in
                      FStar_Pervasives_Native.Some uu____1101 in
                    let e1 =
                      let uu____1120 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1120 in
                    let body =
                      let uu____1122 =
                        let uu____1123 =
                          let uu____1130 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1130] in
                        FStar_List.append gamma uu____1123 in
                      let uu____1135 =
                        let uu____1136 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1139 =
                          let uu____1148 =
                            let uu____1149 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1149 in
                          let uu____1150 = args_of_binders1 gamma in
                          uu____1148 :: uu____1150 in
                        FStar_Syntax_Util.mk_app uu____1136 uu____1139 in
                      FStar_Syntax_Util.abs uu____1122 uu____1135 ret1 in
                    let uu____1153 =
                      let uu____1154 = mk_all_implicit binders in
                      let uu____1161 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1154 uu____1161 in
                    FStar_Syntax_Util.abs uu____1153 body ret1 in
                  let c_push1 =
                    let uu____1193 = mk_lid "push" in
                    register env1 uu____1193 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1213 =
                        let uu____1214 =
                          let uu____1229 = args_of_binders1 binders in
                          (c, uu____1229) in
                        FStar_Syntax_Syntax.Tm_app uu____1214 in
                      mk1 uu____1213
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1239 =
                        let uu____1240 =
                          let uu____1247 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1248 =
                            let uu____1251 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1251] in
                          uu____1247 :: uu____1248 in
                        let uu____1252 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1240 uu____1252 in
                      FStar_Syntax_Syntax.mk_Total uu____1239 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1256 =
                      let uu____1257 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1257 in
                    let uu____1268 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1270 =
                        let uu____1273 =
                          let uu____1282 =
                            let uu____1285 =
                              let uu____1288 =
                                let uu____1297 =
                                  let uu____1298 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1298 in
                                [uu____1297] in
                              FStar_Syntax_Util.mk_app l_ite uu____1288 in
                            [uu____1285] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1282 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1273 in
                      FStar_Syntax_Util.ascribe uu____1270
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1256 uu____1268
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1318 = mk_lid "wp_if_then_else" in
                    register env1 uu____1318 wp_if_then_else in
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
                      let uu____1329 =
                        let uu____1338 =
                          let uu____1341 =
                            let uu____1344 =
                              let uu____1353 =
                                let uu____1356 =
                                  let uu____1359 =
                                    let uu____1368 =
                                      let uu____1369 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1369 in
                                    [uu____1368] in
                                  FStar_Syntax_Util.mk_app l_and uu____1359 in
                                [uu____1356] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1353 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1344 in
                          let uu____1374 =
                            let uu____1379 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1379] in
                          uu____1341 :: uu____1374 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1338 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1329 in
                    let uu____1382 =
                      let uu____1383 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1383 in
                    FStar_Syntax_Util.abs uu____1382 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1395 = mk_lid "wp_assert" in
                    register env1 uu____1395 wp_assert in
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
                      let uu____1406 =
                        let uu____1415 =
                          let uu____1418 =
                            let uu____1421 =
                              let uu____1430 =
                                let uu____1433 =
                                  let uu____1436 =
                                    let uu____1445 =
                                      let uu____1446 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1446 in
                                    [uu____1445] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1436 in
                                [uu____1433] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1430 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1421 in
                          let uu____1451 =
                            let uu____1456 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1456] in
                          uu____1418 :: uu____1451 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1415 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1406 in
                    let uu____1459 =
                      let uu____1460 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1460 in
                    FStar_Syntax_Util.abs uu____1459 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1472 = mk_lid "wp_assume" in
                    register env1 uu____1472 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1481 =
                        let uu____1488 =
                          let uu____1489 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1489 in
                        [uu____1488] in
                      let uu____1490 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1481 uu____1490 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1497 =
                        let uu____1506 =
                          let uu____1509 =
                            let uu____1512 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1512 in
                          let uu____1521 =
                            let uu____1526 =
                              let uu____1529 =
                                let uu____1538 =
                                  let uu____1541 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1541] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1538 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1529 in
                            [uu____1526] in
                          uu____1509 :: uu____1521 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1506 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1497 in
                    let uu____1548 =
                      let uu____1549 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1549 in
                    FStar_Syntax_Util.abs uu____1548 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1561 = mk_lid "wp_close" in
                    register env1 uu____1561 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1571 =
                      let uu____1572 =
                        let uu____1573 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1573 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1572 in
                    FStar_Pervasives_Native.Some uu____1571 in
                  let mk_forall1 x body =
                    let uu____1585 =
                      let uu____1588 =
                        let uu____1589 =
                          let uu____1604 =
                            let uu____1607 =
                              let uu____1608 =
                                let uu____1609 =
                                  let uu____1610 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1610] in
                                FStar_Syntax_Util.abs uu____1609 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1608 in
                            [uu____1607] in
                          (FStar_Syntax_Util.tforall, uu____1604) in
                        FStar_Syntax_Syntax.Tm_app uu____1589 in
                      FStar_Syntax_Syntax.mk uu____1588 in
                    uu____1585 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1620 =
                      let uu____1621 = FStar_Syntax_Subst.compress t in
                      uu____1621.FStar_Syntax_Syntax.n in
                    match uu____1620 with
                    | FStar_Syntax_Syntax.Tm_type uu____1624 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1650  ->
                              match uu____1650 with
                              | (b,uu____1656) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1657 -> true in
                  let rec is_monotonic t =
                    let uu____1662 =
                      let uu____1663 = FStar_Syntax_Subst.compress t in
                      uu____1663.FStar_Syntax_Syntax.n in
                    match uu____1662 with
                    | FStar_Syntax_Syntax.Tm_type uu____1666 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1692  ->
                              match uu____1692 with
                              | (b,uu____1698) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1699 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1751 =
                      let uu____1752 = FStar_Syntax_Subst.compress t1 in
                      uu____1752.FStar_Syntax_Syntax.n in
                    match uu____1751 with
                    | FStar_Syntax_Syntax.Tm_type uu____1755 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1758);
                                      FStar_Syntax_Syntax.pos = uu____1759;
                                      FStar_Syntax_Syntax.vars = uu____1760;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1794 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1794
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1797 =
                              let uu____1800 =
                                let uu____1809 =
                                  let uu____1810 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1810 in
                                [uu____1809] in
                              FStar_Syntax_Util.mk_app x uu____1800 in
                            let uu____1811 =
                              let uu____1814 =
                                let uu____1823 =
                                  let uu____1824 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1824 in
                                [uu____1823] in
                              FStar_Syntax_Util.mk_app y uu____1814 in
                            mk_rel1 b uu____1797 uu____1811 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1829 =
                               let uu____1830 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1833 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1830 uu____1833 in
                             let uu____1836 =
                               let uu____1837 =
                                 let uu____1840 =
                                   let uu____1849 =
                                     let uu____1850 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1850 in
                                   [uu____1849] in
                                 FStar_Syntax_Util.mk_app x uu____1840 in
                               let uu____1851 =
                                 let uu____1854 =
                                   let uu____1863 =
                                     let uu____1864 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1864 in
                                   [uu____1863] in
                                 FStar_Syntax_Util.mk_app y uu____1854 in
                               mk_rel1 b uu____1837 uu____1851 in
                             FStar_Syntax_Util.mk_imp uu____1829 uu____1836 in
                           let uu____1865 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1865)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1868);
                                      FStar_Syntax_Syntax.pos = uu____1869;
                                      FStar_Syntax_Syntax.vars = uu____1870;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1904 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1904
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1907 =
                              let uu____1910 =
                                let uu____1919 =
                                  let uu____1920 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1920 in
                                [uu____1919] in
                              FStar_Syntax_Util.mk_app x uu____1910 in
                            let uu____1921 =
                              let uu____1924 =
                                let uu____1933 =
                                  let uu____1934 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1934 in
                                [uu____1933] in
                              FStar_Syntax_Util.mk_app y uu____1924 in
                            mk_rel1 b uu____1907 uu____1921 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1939 =
                               let uu____1940 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1943 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1940 uu____1943 in
                             let uu____1946 =
                               let uu____1947 =
                                 let uu____1950 =
                                   let uu____1959 =
                                     let uu____1960 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1960 in
                                   [uu____1959] in
                                 FStar_Syntax_Util.mk_app x uu____1950 in
                               let uu____1961 =
                                 let uu____1964 =
                                   let uu____1973 =
                                     let uu____1974 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1974 in
                                   [uu____1973] in
                                 FStar_Syntax_Util.mk_app y uu____1964 in
                               mk_rel1 b uu____1947 uu____1961 in
                             FStar_Syntax_Util.mk_imp uu____1939 uu____1946 in
                           let uu____1975 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1975)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___107_2006 = t1 in
                          let uu____2007 =
                            let uu____2008 =
                              let uu____2021 =
                                let uu____2022 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____2022 in
                              ([binder], uu____2021) in
                            FStar_Syntax_Syntax.Tm_arrow uu____2008 in
                          {
                            FStar_Syntax_Syntax.n = uu____2007;
                            FStar_Syntax_Syntax.pos =
                              (uu___107_2006.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___107_2006.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2037 ->
                        failwith "unhandled arrow"
                    | uu____2050 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2065 =
                        let uu____2066 = FStar_Syntax_Subst.compress t1 in
                        uu____2066.FStar_Syntax_Syntax.n in
                      match uu____2065 with
                      | FStar_Syntax_Syntax.Tm_type uu____2069 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2092 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2092
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2107 =
                                let uu____2108 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2108 i in
                              FStar_Syntax_Syntax.fvar uu____2107
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2135 =
                            let uu____2142 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2156  ->
                                     match uu____2156 with
                                     | (t2,q) ->
                                         let uu____2163 = project i x in
                                         let uu____2164 = project i y in
                                         mk_stronger t2 uu____2163 uu____2164)
                                args in
                            match uu____2142 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2135 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2191);
                                      FStar_Syntax_Syntax.pos = uu____2192;
                                      FStar_Syntax_Syntax.vars = uu____2193;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2231  ->
                                   match uu____2231 with
                                   | (bv,q) ->
                                       let uu____2238 =
                                         let uu____2239 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2239 in
                                       FStar_Syntax_Syntax.gen_bv uu____2238
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2246 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2246) bvs in
                          let body =
                            let uu____2248 = FStar_Syntax_Util.mk_app x args in
                            let uu____2249 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2248 uu____2249 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2256);
                                      FStar_Syntax_Syntax.pos = uu____2257;
                                      FStar_Syntax_Syntax.vars = uu____2258;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2296  ->
                                   match uu____2296 with
                                   | (bv,q) ->
                                       let uu____2303 =
                                         let uu____2304 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2304 in
                                       FStar_Syntax_Syntax.gen_bv uu____2303
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2311 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2311) bvs in
                          let body =
                            let uu____2313 = FStar_Syntax_Util.mk_app x args in
                            let uu____2314 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2313 uu____2314 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2319 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2321 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2322 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2323 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2321 uu____2322 uu____2323 in
                    let uu____2324 =
                      let uu____2325 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2325 in
                    FStar_Syntax_Util.abs uu____2324 body ret_tot_type in
                  let stronger1 =
                    let uu____2353 = mk_lid "stronger" in
                    register env1 uu____2353 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2359 = FStar_Util.prefix gamma in
                    match uu____2359 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2404 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2404 in
                          let uu____2407 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2407 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2417 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2417 in
                              let guard_free1 =
                                let uu____2427 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2427 in
                              let pat =
                                let uu____2431 =
                                  let uu____2440 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2440] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2431 in
                              let pattern_guarded_body =
                                let uu____2444 =
                                  let uu____2445 =
                                    let uu____2452 =
                                      let uu____2453 =
                                        let uu____2464 =
                                          let uu____2467 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2467] in
                                        [uu____2464] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2453 in
                                    (body, uu____2452) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2445 in
                                mk1 uu____2444 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2472 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2476 =
                            let uu____2477 =
                              let uu____2478 =
                                let uu____2479 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2482 =
                                  let uu____2491 = args_of_binders1 wp_args in
                                  let uu____2494 =
                                    let uu____2497 =
                                      let uu____2498 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2498 in
                                    [uu____2497] in
                                  FStar_List.append uu____2491 uu____2494 in
                                FStar_Syntax_Util.mk_app uu____2479
                                  uu____2482 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2478 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2477 in
                          FStar_Syntax_Util.abs gamma uu____2476
                            ret_gtot_type in
                        let uu____2499 =
                          let uu____2500 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2500 in
                        FStar_Syntax_Util.abs uu____2499 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2512 = mk_lid "wp_ite" in
                    register env1 uu____2512 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2518 = FStar_Util.prefix gamma in
                    match uu____2518 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2561 =
                            let uu____2562 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2565 =
                              let uu____2574 =
                                let uu____2575 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2575 in
                              [uu____2574] in
                            FStar_Syntax_Util.mk_app uu____2562 uu____2565 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2561 in
                        let uu____2576 =
                          let uu____2577 =
                            let uu____2584 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2584 gamma in
                          FStar_List.append binders uu____2577 in
                        FStar_Syntax_Util.abs uu____2576 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2600 = mk_lid "null_wp" in
                    register env1 uu____2600 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2609 =
                        let uu____2618 =
                          let uu____2621 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2622 =
                            let uu____2625 =
                              let uu____2628 =
                                let uu____2637 =
                                  let uu____2638 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2638 in
                                [uu____2637] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2628 in
                            let uu____2639 =
                              let uu____2644 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2644] in
                            uu____2625 :: uu____2639 in
                          uu____2621 :: uu____2622 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2618 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2609 in
                    let uu____2647 =
                      let uu____2648 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2648 in
                    FStar_Syntax_Util.abs uu____2647 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2660 = mk_lid "wp_trivial" in
                    register env1 uu____2660 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2665 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2665
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2670 =
                      let uu____2673 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu____2673 in
                    let uu____2708 =
                      let uu___108_2709 = ed in
                      let uu____2710 =
                        let uu____2711 = c wp_if_then_else2 in
                        ([], uu____2711) in
                      let uu____2714 =
                        let uu____2715 = c wp_ite2 in ([], uu____2715) in
                      let uu____2718 =
                        let uu____2719 = c stronger2 in ([], uu____2719) in
                      let uu____2722 =
                        let uu____2723 = c wp_close2 in ([], uu____2723) in
                      let uu____2726 =
                        let uu____2727 = c wp_assert2 in ([], uu____2727) in
                      let uu____2730 =
                        let uu____2731 = c wp_assume2 in ([], uu____2731) in
                      let uu____2734 =
                        let uu____2735 = c null_wp2 in ([], uu____2735) in
                      let uu____2738 =
                        let uu____2739 = c wp_trivial2 in ([], uu____2739) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___108_2709.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___108_2709.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___108_2709.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___108_2709.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___108_2709.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___108_2709.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___108_2709.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2710;
                        FStar_Syntax_Syntax.ite_wp = uu____2714;
                        FStar_Syntax_Syntax.stronger = uu____2718;
                        FStar_Syntax_Syntax.close_wp = uu____2722;
                        FStar_Syntax_Syntax.assert_p = uu____2726;
                        FStar_Syntax_Syntax.assume_p = uu____2730;
                        FStar_Syntax_Syntax.null_wp = uu____2734;
                        FStar_Syntax_Syntax.trivial = uu____2738;
                        FStar_Syntax_Syntax.repr =
                          (uu___108_2709.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___108_2709.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___108_2709.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___108_2709.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2670, uu____2708)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___109_2756 = dmff_env in
      {
        env = env';
        subst = (uu___109_2756.subst);
        tc_const = (uu___109_2756.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2770 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2784 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___95_2796  ->
    match uu___95_2796 with
    | FStar_Syntax_Syntax.Total (t,uu____2798) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___94_2811  ->
                match uu___94_2811 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2812 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2814 =
          let uu____2815 =
            let uu____2816 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2816 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2815 in
        failwith uu____2814
    | FStar_Syntax_Syntax.GTotal uu____2817 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___96_2829  ->
    match uu___96_2829 with
    | N t ->
        let uu____2831 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2831
    | M t ->
        let uu____2833 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2833
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2838,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2840;
                      FStar_Syntax_Syntax.vars = uu____2841;_})
        -> nm_of_comp n2
    | uu____2858 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____2867 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____2867 with | M uu____2868 -> true | N uu____2869 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2874 -> false
let double_star: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ  ->
    let star_once typ1 =
      let uu____2885 =
        let uu____2892 =
          let uu____2893 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2893 in
        [uu____2892] in
      let uu____2894 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2885 uu____2894 in
    let uu____2897 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2897
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
          (let uu____2934 =
             let uu____2947 =
               let uu____2954 =
                 let uu____2959 =
                   let uu____2960 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2960 in
                 let uu____2961 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2959, uu____2961) in
               [uu____2954] in
             let uu____2970 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2947, uu____2970) in
           FStar_Syntax_Syntax.Tm_arrow uu____2934)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2998) ->
          let binders1 =
            FStar_List.map
              (fun uu____3034  ->
                 match uu____3034 with
                 | (bv,aqual) ->
                     let uu____3045 =
                       let uu___110_3046 = bv in
                       let uu____3047 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___110_3046.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___110_3046.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3047
                       } in
                     (uu____3045, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3050,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3052);
                             FStar_Syntax_Syntax.pos = uu____3053;
                             FStar_Syntax_Syntax.vars = uu____3054;_})
               ->
               let uu____3079 =
                 let uu____3080 =
                   let uu____3093 =
                     let uu____3094 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3094 in
                   (binders1, uu____3093) in
                 FStar_Syntax_Syntax.Tm_arrow uu____3080 in
               mk1 uu____3079
           | uu____3101 ->
               let uu____3102 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3102 with
                | N hn ->
                    let uu____3104 =
                      let uu____3105 =
                        let uu____3118 =
                          let uu____3119 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3119 in
                        (binders1, uu____3118) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3105 in
                    mk1 uu____3104
                | M a ->
                    let uu____3127 =
                      let uu____3128 =
                        let uu____3141 =
                          let uu____3148 =
                            let uu____3155 =
                              let uu____3160 =
                                let uu____3161 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3161 in
                              let uu____3162 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3160, uu____3162) in
                            [uu____3155] in
                          FStar_List.append binders1 uu____3148 in
                        let uu____3175 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3141, uu____3175) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3128 in
                    mk1 uu____3127))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3241 = f x in
                    FStar_Util.string_builder_append strb uu____3241);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3248 = f x1 in
                         FStar_Util.string_builder_append strb uu____3248))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3250 = FStar_Syntax_Print.term_to_string t2 in
            let uu____3251 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____3250 uu____3251 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3259 =
              let uu____3260 = FStar_Syntax_Subst.compress ty in
              uu____3260.FStar_Syntax_Syntax.n in
            match uu____3259 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3281 =
                  let uu____3282 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3282 in
                if uu____3281
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3308 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3308 s in
                       let uu____3311 =
                         let uu____3312 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3312 in
                       if uu____3311
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else () in
                     let uu____3315 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3315 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3337  ->
                                  match uu____3337 with
                                  | (bv,uu____3347) ->
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
            | uu____3361 ->
                ((let uu____3363 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____3363);
                 false) in
          let rec is_valid_application head2 =
            let uu____3368 =
              let uu____3369 = FStar_Syntax_Subst.compress head2 in
              uu____3369.FStar_Syntax_Syntax.n in
            match uu____3368 with
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
                  (let uu____3374 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3374)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3376 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3376 with
                 | ((uu____3385,ty),uu____3387) ->
                     let uu____3392 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3392
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3400 -> true
                        | uu____3415 ->
                            ((let uu____3417 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____3417);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3419 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3420 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3422) ->
                is_valid_application t2
            | uu____3427 -> false in
          let uu____3428 = is_valid_application head1 in
          if uu____3428
          then
            let uu____3429 =
              let uu____3430 =
                let uu____3445 =
                  FStar_List.map
                    (fun uu____3466  ->
                       match uu____3466 with
                       | (t2,qual) ->
                           let uu____3483 = star_type' env t2 in
                           (uu____3483, qual)) args in
                (head1, uu____3445) in
              FStar_Syntax_Syntax.Tm_app uu____3430 in
            mk1 uu____3429
          else
            (let uu____3493 =
               let uu____3494 =
                 let uu____3495 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3495 in
               FStar_Errors.Err uu____3494 in
             FStar_Exn.raise uu____3493)
      | FStar_Syntax_Syntax.Tm_bvar uu____3496 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3497 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3498 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3499 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3523 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3523 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___113_3531 = env in
                 let uu____3532 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3532;
                   subst = (uu___113_3531.subst);
                   tc_const = (uu___113_3531.tc_const)
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
               ((let uu___114_3552 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___114_3552.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___114_3552.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3559 =
            let uu____3560 =
              let uu____3567 = star_type' env t2 in (uu____3567, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3560 in
          mk1 uu____3559
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3615 =
            let uu____3616 =
              let uu____3643 = star_type' env e in
              let uu____3644 =
                let uu____3659 =
                  let uu____3666 = star_type' env t2 in
                  FStar_Util.Inl uu____3666 in
                (uu____3659, FStar_Pervasives_Native.None) in
              (uu____3643, uu____3644, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3616 in
          mk1 uu____3615
      | FStar_Syntax_Syntax.Tm_ascribed uu____3697 ->
          let uu____3724 =
            let uu____3725 =
              let uu____3726 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____3726 in
            FStar_Errors.Err uu____3725 in
          FStar_Exn.raise uu____3724
      | FStar_Syntax_Syntax.Tm_refine uu____3727 ->
          let uu____3734 =
            let uu____3735 =
              let uu____3736 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3736 in
            FStar_Errors.Err uu____3735 in
          FStar_Exn.raise uu____3734
      | FStar_Syntax_Syntax.Tm_uinst uu____3737 ->
          let uu____3744 =
            let uu____3745 =
              let uu____3746 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3746 in
            FStar_Errors.Err uu____3745 in
          FStar_Exn.raise uu____3744
      | FStar_Syntax_Syntax.Tm_constant uu____3747 ->
          let uu____3748 =
            let uu____3749 =
              let uu____3750 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3750 in
            FStar_Errors.Err uu____3749 in
          FStar_Exn.raise uu____3748
      | FStar_Syntax_Syntax.Tm_match uu____3751 ->
          let uu____3774 =
            let uu____3775 =
              let uu____3776 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3776 in
            FStar_Errors.Err uu____3775 in
          FStar_Exn.raise uu____3774
      | FStar_Syntax_Syntax.Tm_let uu____3777 ->
          let uu____3790 =
            let uu____3791 =
              let uu____3792 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____3792 in
            FStar_Errors.Err uu____3791 in
          FStar_Exn.raise uu____3790
      | FStar_Syntax_Syntax.Tm_uvar uu____3793 ->
          let uu____3810 =
            let uu____3811 =
              let uu____3812 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____3812 in
            FStar_Errors.Err uu____3811 in
          FStar_Exn.raise uu____3810
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____3813 =
            let uu____3814 =
              let uu____3815 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____3815 in
            FStar_Errors.Err uu____3814 in
          FStar_Exn.raise uu____3813
      | FStar_Syntax_Syntax.Tm_delayed uu____3816 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___98_3846  ->
    match uu___98_3846 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___97_3853  ->
                match uu___97_3853 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3854 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3859 =
      let uu____3860 = FStar_Syntax_Subst.compress t in
      uu____3860.FStar_Syntax_Syntax.n in
    match uu____3859 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3886 =
            let uu____3887 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____3887 in
          is_C uu____3886 in
        if r
        then
          ((let uu____3903 =
              let uu____3904 =
                FStar_List.for_all
                  (fun uu____3912  ->
                     match uu____3912 with | (h,uu____3918) -> is_C h) args in
              Prims.op_Negation uu____3904 in
            if uu____3903 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3922 =
              let uu____3923 =
                FStar_List.for_all
                  (fun uu____3932  ->
                     match uu____3932 with
                     | (h,uu____3938) ->
                         let uu____3939 = is_C h in
                         Prims.op_Negation uu____3939) args in
              Prims.op_Negation uu____3923 in
            if uu____3922 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3959 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3959 with
         | M t1 ->
             ((let uu____3962 = is_C t1 in
               if uu____3962 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3966) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3972) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3978,uu____3979) -> is_C t1
    | uu____4020 -> false
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
          let uu____4046 =
            let uu____4047 =
              let uu____4062 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____4063 =
                let uu____4070 =
                  let uu____4075 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____4075) in
                [uu____4070] in
              (uu____4062, uu____4063) in
            FStar_Syntax_Syntax.Tm_app uu____4047 in
          mk1 uu____4046 in
        let uu____4090 =
          let uu____4091 = FStar_Syntax_Syntax.mk_binder p in [uu____4091] in
        FStar_Syntax_Util.abs uu____4090 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___99_4095  ->
    match uu___99_4095 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4096 -> false
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
        let return_if uu____4271 =
          match uu____4271 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4298 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4300 =
                       let uu____4301 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4301 in
                     Prims.op_Negation uu____4300) in
                if uu____4298
                then
                  let uu____4302 =
                    let uu____4303 =
                      let uu____4304 = FStar_Syntax_Print.term_to_string e in
                      let uu____4305 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4306 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4304 uu____4305 uu____4306 in
                    FStar_Errors.Err uu____4303 in
                  FStar_Exn.raise uu____4302
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4323 = mk_return env t1 s_e in
                     ((M t1), uu____4323, u_e)))
               | (M t1,N t2) ->
                   let uu____4326 =
                     let uu____4327 =
                       let uu____4328 = FStar_Syntax_Print.term_to_string e in
                       let uu____4329 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4330 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4328 uu____4329 uu____4330 in
                     FStar_Errors.Err uu____4327 in
                   FStar_Exn.raise uu____4326) in
        let ensure_m env1 e2 =
          let strip_m uu___100_4371 =
            match uu___100_4371 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4387 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4407 =
                let uu____4408 =
                  let uu____4413 =
                    let uu____4414 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____4414 in
                  (uu____4413, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____4408 in
              FStar_Exn.raise uu____4407
          | M uu____4421 ->
              let uu____4422 = check env1 e2 context_nm in strip_m uu____4422 in
        let uu____4429 =
          let uu____4430 = FStar_Syntax_Subst.compress e in
          uu____4430.FStar_Syntax_Syntax.n in
        match uu____4429 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4439 ->
            let uu____4440 = infer env e in return_if uu____4440
        | FStar_Syntax_Syntax.Tm_name uu____4447 ->
            let uu____4448 = infer env e in return_if uu____4448
        | FStar_Syntax_Syntax.Tm_fvar uu____4455 ->
            let uu____4456 = infer env e in return_if uu____4456
        | FStar_Syntax_Syntax.Tm_abs uu____4463 ->
            let uu____4480 = infer env e in return_if uu____4480
        | FStar_Syntax_Syntax.Tm_constant uu____4487 ->
            let uu____4488 = infer env e in return_if uu____4488
        | FStar_Syntax_Syntax.Tm_app uu____4495 ->
            let uu____4510 = infer env e in return_if uu____4510
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4578) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4584) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4590,uu____4591) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4632 ->
            let uu____4645 =
              let uu____4646 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4646 in
            failwith uu____4645
        | FStar_Syntax_Syntax.Tm_type uu____4653 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4660 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4679 ->
            let uu____4686 =
              let uu____4687 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4687 in
            failwith uu____4686
        | FStar_Syntax_Syntax.Tm_uvar uu____4694 ->
            let uu____4711 =
              let uu____4712 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4712 in
            failwith uu____4711
        | FStar_Syntax_Syntax.Tm_delayed uu____4719 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4750 =
              let uu____4751 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4751 in
            failwith uu____4750
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
      let uu____4775 =
        let uu____4776 = FStar_Syntax_Subst.compress e in
        uu____4776.FStar_Syntax_Syntax.n in
      match uu____4775 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____4835;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____4836;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____4842 =
                  let uu___115_4843 = rc in
                  let uu____4844 =
                    let uu____4849 =
                      let uu____4850 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____4850 in
                    FStar_Pervasives_Native.Some uu____4849 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___115_4843.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____4844;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___115_4843.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____4842 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___116_4860 = env in
            let uu____4861 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____4861;
              subst = (uu___116_4860.subst);
              tc_const = (uu___116_4860.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____4881  ->
                 match uu____4881 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___117_4894 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___117_4894.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___117_4894.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____4895 =
            FStar_List.fold_left
              (fun uu____4924  ->
                 fun uu____4925  ->
                   match (uu____4924, uu____4925) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____4973 = is_C c in
                       if uu____4973
                       then
                         let xw =
                           let uu____4981 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____4981 in
                         let x =
                           let uu___118_4983 = bv in
                           let uu____4984 =
                             let uu____4987 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____4987 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___118_4983.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___118_4983.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____4984
                           } in
                         let env3 =
                           let uu___119_4989 = env2 in
                           let uu____4990 =
                             let uu____4993 =
                               let uu____4994 =
                                 let uu____5001 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____5001) in
                               FStar_Syntax_Syntax.NT uu____4994 in
                             uu____4993 :: (env2.subst) in
                           {
                             env = (uu___119_4989.env);
                             subst = uu____4990;
                             tc_const = (uu___119_4989.tc_const)
                           } in
                         let uu____5002 =
                           let uu____5005 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____5006 =
                             let uu____5009 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____5009 :: acc in
                           uu____5005 :: uu____5006 in
                         (env3, uu____5002)
                       else
                         (let x =
                            let uu___120_5014 = bv in
                            let uu____5015 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___120_5014.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___120_5014.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5015
                            } in
                          let uu____5018 =
                            let uu____5021 = FStar_Syntax_Syntax.mk_binder x in
                            uu____5021 :: acc in
                          (env2, uu____5018))) (env1, []) binders1 in
          (match uu____4895 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____5041 =
                 let check_what =
                   let uu____5059 = is_monadic rc_opt1 in
                   if uu____5059 then check_m else check_n in
                 let uu____5071 = check_what env2 body1 in
                 match uu____5071 with
                 | (t,s_body,u_body) ->
                     let uu____5087 =
                       let uu____5088 =
                         let uu____5089 = is_monadic rc_opt1 in
                         if uu____5089 then M t else N t in
                       comp_of_nm uu____5088 in
                     (uu____5087, s_body, u_body) in
               (match uu____5041 with
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
                                 let uu____5114 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___101_5118  ->
                                           match uu___101_5118 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5119 -> false)) in
                                 if uu____5114
                                 then
                                   let uu____5120 =
                                     FStar_List.filter
                                       (fun uu___102_5124  ->
                                          match uu___102_5124 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5125 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5120
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5134 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___103_5138  ->
                                         match uu___103_5138 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5139 -> false)) in
                               if uu____5134
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___104_5146  ->
                                        match uu___104_5146 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5147 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5148 =
                                   let uu____5149 =
                                     let uu____5154 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5154 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5149 flags in
                                 FStar_Pervasives_Native.Some uu____5148
                               else
                                 (let uu____5156 =
                                    let uu___121_5157 = rc in
                                    let uu____5158 =
                                      let uu____5163 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5163 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___121_5157.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5158;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___121_5157.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5156)) in
                    let uu____5164 =
                      let comp1 =
                        let uu____5174 = is_monadic rc_opt1 in
                        let uu____5175 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5174 uu____5175 in
                      let uu____5176 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5176,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5164 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5218 =
                             let uu____5219 =
                               let uu____5236 =
                                 let uu____5239 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5239 s_rc_opt in
                               (s_binders1, s_body1, uu____5236) in
                             FStar_Syntax_Syntax.Tm_abs uu____5219 in
                           mk1 uu____5218 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5249 =
                             let uu____5250 =
                               let uu____5267 =
                                 let uu____5270 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5270 u_rc_opt in
                               (u_binders2, u_body2, uu____5267) in
                             FStar_Syntax_Syntax.Tm_abs uu____5250 in
                           mk1 uu____5249 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5280;_};
            FStar_Syntax_Syntax.fv_delta = uu____5281;
            FStar_Syntax_Syntax.fv_qual = uu____5282;_}
          ->
          let uu____5285 =
            let uu____5290 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5290 in
          (match uu____5285 with
           | (uu____5321,t) ->
               let uu____5323 = let uu____5324 = normalize1 t in N uu____5324 in
               (uu____5323, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____5347 = check_n env head1 in
          (match uu____5347 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____5367 =
                   let uu____5368 = FStar_Syntax_Subst.compress t in
                   uu____5368.FStar_Syntax_Syntax.n in
                 match uu____5367 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____5371 -> true
                 | uu____5384 -> false in
               let rec flatten1 t =
                 let uu____5401 =
                   let uu____5402 = FStar_Syntax_Subst.compress t in
                   uu____5402.FStar_Syntax_Syntax.n in
                 match uu____5401 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____5419);
                                FStar_Syntax_Syntax.pos = uu____5420;
                                FStar_Syntax_Syntax.vars = uu____5421;_})
                     when is_arrow t1 ->
                     let uu____5446 = flatten1 t1 in
                     (match uu____5446 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5528,uu____5529)
                     -> flatten1 e1
                 | uu____5570 ->
                     let uu____5571 =
                       let uu____5572 =
                         let uu____5573 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____5573 in
                       FStar_Errors.Err uu____5572 in
                     FStar_Exn.raise uu____5571 in
               let uu____5586 = flatten1 t_head in
               (match uu____5586 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____5646 =
                          let uu____5647 =
                            let uu____5648 = FStar_Util.string_of_int n1 in
                            let uu____5655 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____5666 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____5648 uu____5655 uu____5666 in
                          FStar_Errors.Err uu____5647 in
                        FStar_Exn.raise uu____5646)
                     else ();
                     (let uu____5674 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____5674 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____5715 args1 =
                            match uu____5715 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____5789 =
                                       let uu____5790 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____5790.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____5789
                                 | (binders3,[]) ->
                                     let uu____5820 =
                                       let uu____5821 =
                                         let uu____5824 =
                                           let uu____5825 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____5825 in
                                         FStar_Syntax_Subst.compress
                                           uu____5824 in
                                       uu____5821.FStar_Syntax_Syntax.n in
                                     (match uu____5820 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____5850 =
                                            let uu____5851 =
                                              let uu____5852 =
                                                let uu____5865 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____5865) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____5852 in
                                            mk1 uu____5851 in
                                          N uu____5850
                                      | uu____5872 -> failwith "wat?")
                                 | ([],uu____5873::uu____5874) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____5914)::binders3,(arg,uu____5917)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____5970 = FStar_List.splitAt n' binders1 in
                          (match uu____5970 with
                           | (binders2,uu____6002) ->
                               let uu____6027 =
                                 let uu____6046 =
                                   FStar_List.map2
                                     (fun uu____6094  ->
                                        fun uu____6095  ->
                                          match (uu____6094, uu____6095) with
                                          | ((bv,uu____6127),(arg,q)) ->
                                              let uu____6138 =
                                                let uu____6139 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____6139.FStar_Syntax_Syntax.n in
                                              (match uu____6138 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____6156 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____6180 ->
                                                   let uu____6181 =
                                                     check_n env arg in
                                                   (match uu____6181 with
                                                    | (uu____6202,s_arg,u_arg)
                                                        ->
                                                        let uu____6205 =
                                                          let uu____6212 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____6212
                                                          then
                                                            let uu____6219 =
                                                              let uu____6224
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____6224, q) in
                                                            [uu____6219;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____6205))))
                                     binders2 args in
                                 FStar_List.split uu____6046 in
                               (match uu____6027 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____6313 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____6322 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____6313, uu____6322)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6388) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____6394) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6400,uu____6401) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____6443 = let uu____6444 = env.tc_const c in N uu____6444 in
          (uu____6443, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____6445 ->
          let uu____6458 =
            let uu____6459 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____6459 in
          failwith uu____6458
      | FStar_Syntax_Syntax.Tm_type uu____6466 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____6473 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____6492 ->
          let uu____6499 =
            let uu____6500 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____6500 in
          failwith uu____6499
      | FStar_Syntax_Syntax.Tm_uvar uu____6507 ->
          let uu____6524 =
            let uu____6525 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____6525 in
          failwith uu____6524
      | FStar_Syntax_Syntax.Tm_delayed uu____6532 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6563 =
            let uu____6564 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____6564 in
          failwith uu____6563
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
          let uu____6609 = check_n env e0 in
          match uu____6609 with
          | (uu____6622,s_e0,u_e0) ->
              let uu____6625 =
                let uu____6654 =
                  FStar_List.map
                    (fun b  ->
                       let uu____6715 = FStar_Syntax_Subst.open_branch b in
                       match uu____6715 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___122_6757 = env in
                             let uu____6758 =
                               let uu____6759 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____6759 in
                             {
                               env = uu____6758;
                               subst = (uu___122_6757.subst);
                               tc_const = (uu___122_6757.tc_const)
                             } in
                           let uu____6762 = f env1 body in
                           (match uu____6762 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____6834 ->
                           FStar_Exn.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____6654 in
              (match uu____6625 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____6936 = FStar_List.hd nms in
                     match uu____6936 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___105_6942  ->
                          match uu___105_6942 with
                          | M uu____6943 -> true
                          | uu____6944 -> false) nms in
                   let uu____6945 =
                     let uu____6982 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____7072  ->
                              match uu____7072 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____7249 =
                                         check env original_body (M t2) in
                                       (match uu____7249 with
                                        | (uu____7286,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____7325,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____6982 in
                   (match uu____6945 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____7509  ->
                                 match uu____7509 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____7560 =
                                         let uu____7561 =
                                           let uu____7576 =
                                             let uu____7583 =
                                               let uu____7588 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____7589 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____7588, uu____7589) in
                                             [uu____7583] in
                                           (s_body, uu____7576) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____7561 in
                                       mk1 uu____7560 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____7621 =
                              let uu____7622 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____7622] in
                            let uu____7623 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____7621 uu____7623
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____7629 =
                              let uu____7636 =
                                let uu____7637 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____7637 in
                              [uu____7636] in
                            let uu____7638 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____7629 uu____7638 in
                          let uu____7641 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____7680 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____7641, uu____7680)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____7697 =
                             let uu____7700 =
                               let uu____7701 =
                                 let uu____7728 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____7728,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____7701 in
                             mk1 uu____7700 in
                           let uu____7765 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____7697, uu____7765))))
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
              let uu____7812 = FStar_Syntax_Syntax.mk_binder x in
              [uu____7812] in
            let uu____7813 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____7813 with
            | (x_binders1,e21) ->
                let uu____7826 = infer env e1 in
                (match uu____7826 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____7843 = is_C t1 in
                       if uu____7843
                       then
                         let uu___123_7844 = binding in
                         let uu____7845 =
                           let uu____7848 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____7848 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___123_7844.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_7844.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____7845;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_7844.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___123_7844.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___124_7851 = env in
                       let uu____7852 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_7854 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_7854.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_7854.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____7852;
                         subst = (uu___124_7851.subst);
                         tc_const = (uu___124_7851.tc_const)
                       } in
                     let uu____7855 = proceed env1 e21 in
                     (match uu____7855 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___126_7872 = binding in
                            let uu____7873 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___126_7872.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___126_7872.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____7873;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___126_7872.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___126_7872.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____7876 =
                            let uu____7879 =
                              let uu____7880 =
                                let uu____7893 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___127_7903 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___127_7903.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___127_7903.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___127_7903.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___127_7903.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____7893) in
                              FStar_Syntax_Syntax.Tm_let uu____7880 in
                            mk1 uu____7879 in
                          let uu____7904 =
                            let uu____7907 =
                              let uu____7908 =
                                let uu____7921 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_7931 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_7931.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_7931.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_7931.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_7931.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____7921) in
                              FStar_Syntax_Syntax.Tm_let uu____7908 in
                            mk1 uu____7907 in
                          (nm_rec, uu____7876, uu____7904))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___129_7940 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___129_7940.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___129_7940.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___129_7940.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___130_7942 = env in
                       let uu____7943 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___131_7945 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___131_7945.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___131_7945.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____7943;
                         subst = (uu___130_7942.subst);
                         tc_const = (uu___130_7942.tc_const)
                       } in
                     let uu____7946 = ensure_m env1 e21 in
                     (match uu____7946 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____7969 =
                              let uu____7970 =
                                let uu____7985 =
                                  let uu____7992 =
                                    let uu____7997 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____7998 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____7997, uu____7998) in
                                  [uu____7992] in
                                (s_e2, uu____7985) in
                              FStar_Syntax_Syntax.Tm_app uu____7970 in
                            mk1 uu____7969 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____8017 =
                              let uu____8018 =
                                let uu____8033 =
                                  let uu____8040 =
                                    let uu____8045 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____8045) in
                                  [uu____8040] in
                                (s_e1, uu____8033) in
                              FStar_Syntax_Syntax.Tm_app uu____8018 in
                            mk1 uu____8017 in
                          let uu____8060 =
                            let uu____8061 =
                              let uu____8062 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____8062] in
                            FStar_Syntax_Util.abs uu____8061 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____8063 =
                            let uu____8066 =
                              let uu____8067 =
                                let uu____8080 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___132_8090 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___132_8090.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___132_8090.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___132_8090.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___132_8090.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8080) in
                              FStar_Syntax_Syntax.Tm_let uu____8067 in
                            mk1 uu____8066 in
                          ((M t2), uu____8060, uu____8063)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8102 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____8102 in
      let uu____8103 = check env e mn in
      match uu____8103 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8119 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8141 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____8141 in
      let uu____8142 = check env e mn in
      match uu____8142 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8158 -> failwith "[check_m]: impossible"
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
        (let uu____8188 =
           let uu____8189 = is_C c in Prims.op_Negation uu____8189 in
         if uu____8188 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____8197 =
           let uu____8198 = FStar_Syntax_Subst.compress c in
           uu____8198.FStar_Syntax_Syntax.n in
         match uu____8197 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____8223 = FStar_Syntax_Util.head_and_args wp in
             (match uu____8223 with
              | (wp_head,wp_args) ->
                  ((let uu____8261 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____8275 =
                           let uu____8276 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____8276 in
                         Prims.op_Negation uu____8275) in
                    if uu____8261 then failwith "mismatch" else ());
                   (let uu____8284 =
                      let uu____8285 =
                        let uu____8300 =
                          FStar_List.map2
                            (fun uu____8328  ->
                               fun uu____8329  ->
                                 match (uu____8328, uu____8329) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____8366 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____8366
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____8369 = print_implicit q in
                                         let uu____8370 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____8369 uu____8370)
                                      else ();
                                      (let uu____8372 =
                                         trans_F_ env arg wp_arg in
                                       (uu____8372, q)))) args wp_args in
                        (head1, uu____8300) in
                      FStar_Syntax_Syntax.Tm_app uu____8285 in
                    mk1 uu____8284)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____8406 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____8406 with
              | (binders_orig,comp1) ->
                  let uu____8413 =
                    let uu____8428 =
                      FStar_List.map
                        (fun uu____8462  ->
                           match uu____8462 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____8482 = is_C h in
                               if uu____8482
                               then
                                 let w' =
                                   let uu____8494 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____8494 in
                                 let uu____8495 =
                                   let uu____8502 =
                                     let uu____8509 =
                                       let uu____8514 =
                                         let uu____8515 =
                                           let uu____8516 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____8516 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____8515 in
                                       (uu____8514, q) in
                                     [uu____8509] in
                                   (w', q) :: uu____8502 in
                                 (w', uu____8495)
                               else
                                 (let x =
                                    let uu____8537 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____8537 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____8428 in
                  (match uu____8413 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____8592 =
                           let uu____8595 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____8595 in
                         FStar_Syntax_Subst.subst_comp uu____8592 comp1 in
                       let app =
                         let uu____8599 =
                           let uu____8600 =
                             let uu____8615 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____8630 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____8631 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8630, uu____8631)) bvs in
                             (wp, uu____8615) in
                           FStar_Syntax_Syntax.Tm_app uu____8600 in
                         mk1 uu____8599 in
                       let comp3 =
                         let uu____8639 = type_of_comp comp2 in
                         let uu____8640 = is_monadic_comp comp2 in
                         trans_G env uu____8639 uu____8640 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____8642,uu____8643) ->
             trans_F_ env e wp
         | uu____8684 -> failwith "impossible trans_F_")
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
            let uu____8689 =
              let uu____8690 = star_type' env h in
              let uu____8693 =
                let uu____8702 =
                  let uu____8707 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____8707) in
                [uu____8702] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____8690;
                FStar_Syntax_Syntax.effect_args = uu____8693;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____8689
          else
            (let uu____8717 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____8717)
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
    fun t  -> let uu____8732 = n env.env t in star_type' env uu____8732
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____8749 = n env.env t in check_n env uu____8749
let trans_F:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____8762 = n env.env c in
        let uu____8763 = n env.env wp in trans_F_ env uu____8762 uu____8763