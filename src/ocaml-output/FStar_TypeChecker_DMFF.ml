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
                        let uu____267 = FStar_ST.read sigelts in sigelt ::
                          uu____267 in
                      FStar_ST.write sigelts uu____264);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____305  ->
                     match uu____305 with
                     | (t,b) ->
                         let uu____316 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____316)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____347 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____347)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____370 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____370) in
              let uu____371 =
                let uu____386 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____408 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____408 in
                    let uu____411 =
                      let uu____412 =
                        let uu____419 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____420 =
                          let uu____423 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____423] in
                        uu____419 :: uu____420 in
                      FStar_List.append binders uu____412 in
                    FStar_Syntax_Util.abs uu____411 body
                      FStar_Pervasives_Native.None in
                  let uu____428 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____429 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____428, uu____429) in
                match uu____386 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____463 =
                        let uu____464 =
                          let uu____479 =
                            let uu____486 =
                              FStar_List.map
                                (fun uu____506  ->
                                   match uu____506 with
                                   | (bv,uu____516) ->
                                       let uu____517 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____518 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____517, uu____518)) binders in
                            let uu____519 =
                              let uu____526 =
                                let uu____531 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____532 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____531, uu____532) in
                              let uu____533 =
                                let uu____540 =
                                  let uu____545 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____545) in
                                [uu____540] in
                              uu____526 :: uu____533 in
                            FStar_List.append uu____486 uu____519 in
                          (fv, uu____479) in
                        FStar_Syntax_Syntax.Tm_app uu____464 in
                      mk1 uu____463 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____371 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____604 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____604 in
                    let ret1 =
                      let uu____608 =
                        let uu____609 =
                          let uu____612 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____612 in
                        FStar_Syntax_Util.residual_tot uu____609 in
                      FStar_Pervasives_Native.Some uu____608 in
                    let body =
                      let uu____614 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____614 ret1 in
                    let uu____615 =
                      let uu____616 = mk_all_implicit binders in
                      let uu____623 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____616 uu____623 in
                    FStar_Syntax_Util.abs uu____615 body ret1 in
                  let c_pure1 =
                    let uu____651 = mk_lid "pure" in
                    register env1 uu____651 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____656 =
                        let uu____657 =
                          let uu____658 =
                            let uu____665 =
                              let uu____666 =
                                let uu____667 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____667 in
                              FStar_Syntax_Syntax.mk_binder uu____666 in
                            [uu____665] in
                          let uu____668 =
                            let uu____671 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____671 in
                          FStar_Syntax_Util.arrow uu____658 uu____668 in
                        mk_gctx uu____657 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____656 in
                    let r =
                      let uu____673 =
                        let uu____674 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____674 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____673 in
                    let ret1 =
                      let uu____678 =
                        let uu____679 =
                          let uu____682 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____682 in
                        FStar_Syntax_Util.residual_tot uu____679 in
                      FStar_Pervasives_Native.Some uu____678 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____690 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____693 =
                          let uu____702 =
                            let uu____705 =
                              let uu____706 =
                                let uu____707 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____707
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____706 in
                            [uu____705] in
                          FStar_List.append gamma_as_args uu____702 in
                        FStar_Syntax_Util.mk_app uu____690 uu____693 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____710 =
                      let uu____711 = mk_all_implicit binders in
                      let uu____718 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____711 uu____718 in
                    FStar_Syntax_Util.abs uu____710 outer_body ret1 in
                  let c_app1 =
                    let uu____754 = mk_lid "app" in
                    register env1 uu____754 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____761 =
                        let uu____768 =
                          let uu____769 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____769 in
                        [uu____768] in
                      let uu____770 =
                        let uu____773 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____773 in
                      FStar_Syntax_Util.arrow uu____761 uu____770 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____776 =
                        let uu____777 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____777 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____776 in
                    let ret1 =
                      let uu____781 =
                        let uu____782 =
                          let uu____785 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____785 in
                        FStar_Syntax_Util.residual_tot uu____782 in
                      FStar_Pervasives_Native.Some uu____781 in
                    let uu____786 =
                      let uu____787 = mk_all_implicit binders in
                      let uu____794 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____787 uu____794 in
                    let uu____829 =
                      let uu____830 =
                        let uu____839 =
                          let uu____842 =
                            let uu____845 =
                              let uu____854 =
                                let uu____857 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____857] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____854 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____845 in
                          let uu____858 =
                            let uu____863 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____863] in
                          uu____842 :: uu____858 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____839 in
                      FStar_Syntax_Util.mk_app c_app1 uu____830 in
                    FStar_Syntax_Util.abs uu____786 uu____829 ret1 in
                  let c_lift11 =
                    let uu____867 = mk_lid "lift1" in
                    register env1 uu____867 c_lift1 in
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
                      let uu____875 =
                        let uu____882 =
                          let uu____883 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____883 in
                        let uu____884 =
                          let uu____887 =
                            let uu____888 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____888 in
                          [uu____887] in
                        uu____882 :: uu____884 in
                      let uu____889 =
                        let uu____892 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____892 in
                      FStar_Syntax_Util.arrow uu____875 uu____889 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____895 =
                        let uu____896 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____896 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____895 in
                    let a2 =
                      let uu____898 =
                        let uu____899 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____899 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____898 in
                    let ret1 =
                      let uu____903 =
                        let uu____904 =
                          let uu____907 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____907 in
                        FStar_Syntax_Util.residual_tot uu____904 in
                      FStar_Pervasives_Native.Some uu____903 in
                    let uu____908 =
                      let uu____909 = mk_all_implicit binders in
                      let uu____916 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____909 uu____916 in
                    let uu____959 =
                      let uu____960 =
                        let uu____969 =
                          let uu____972 =
                            let uu____975 =
                              let uu____984 =
                                let uu____987 =
                                  let uu____990 =
                                    let uu____999 =
                                      let uu____1002 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____1002] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____999 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____990 in
                                let uu____1003 =
                                  let uu____1008 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____1008] in
                                uu____987 :: uu____1003 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____984 in
                            FStar_Syntax_Util.mk_app c_app1 uu____975 in
                          let uu____1011 =
                            let uu____1016 =
                              FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____1016] in
                          uu____972 :: uu____1011 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____969 in
                      FStar_Syntax_Util.mk_app c_app1 uu____960 in
                    FStar_Syntax_Util.abs uu____908 uu____959 ret1 in
                  let c_lift21 =
                    let uu____1020 = mk_lid "lift2" in
                    register env1 uu____1020 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1027 =
                        let uu____1034 =
                          let uu____1035 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____1035 in
                        [uu____1034] in
                      let uu____1036 =
                        let uu____1039 =
                          let uu____1040 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____1040 in
                        FStar_Syntax_Syntax.mk_Total uu____1039 in
                      FStar_Syntax_Util.arrow uu____1027 uu____1036 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____1045 =
                        let uu____1046 =
                          let uu____1049 =
                            let uu____1050 =
                              let uu____1057 =
                                let uu____1058 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____1058 in
                              [uu____1057] in
                            let uu____1059 =
                              let uu____1062 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____1062 in
                            FStar_Syntax_Util.arrow uu____1050 uu____1059 in
                          mk_ctx uu____1049 in
                        FStar_Syntax_Util.residual_tot uu____1046 in
                      FStar_Pervasives_Native.Some uu____1045 in
                    let e1 =
                      let uu____1064 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1064 in
                    let body =
                      let uu____1066 =
                        let uu____1067 =
                          let uu____1074 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____1074] in
                        FStar_List.append gamma uu____1067 in
                      let uu____1079 =
                        let uu____1080 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____1083 =
                          let uu____1092 =
                            let uu____1093 =
                              FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____1093 in
                          let uu____1094 = args_of_binders1 gamma in
                          uu____1092 :: uu____1094 in
                        FStar_Syntax_Util.mk_app uu____1080 uu____1083 in
                      FStar_Syntax_Util.abs uu____1066 uu____1079 ret1 in
                    let uu____1097 =
                      let uu____1098 = mk_all_implicit binders in
                      let uu____1105 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____1098 uu____1105 in
                    FStar_Syntax_Util.abs uu____1097 body ret1 in
                  let c_push1 =
                    let uu____1137 = mk_lid "push" in
                    register env1 uu____1137 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1157 =
                        let uu____1158 =
                          let uu____1173 = args_of_binders1 binders in
                          (c, uu____1173) in
                        FStar_Syntax_Syntax.Tm_app uu____1158 in
                      mk1 uu____1157
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1183 =
                        let uu____1184 =
                          let uu____1191 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1192 =
                            let uu____1195 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1195] in
                          uu____1191 :: uu____1192 in
                        let uu____1196 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1184 uu____1196 in
                      FStar_Syntax_Syntax.mk_Total uu____1183 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____1200 =
                      let uu____1201 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1201 in
                    let uu____1212 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____1214 =
                        let uu____1217 =
                          let uu____1226 =
                            let uu____1229 =
                              let uu____1232 =
                                let uu____1241 =
                                  let uu____1242 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1242 in
                                [uu____1241] in
                              FStar_Syntax_Util.mk_app l_ite uu____1232 in
                            [uu____1229] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1226 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1217 in
                      FStar_Syntax_Util.ascribe uu____1214
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____1200 uu____1212
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____1262 = mk_lid "wp_if_then_else" in
                    register env1 uu____1262 wp_if_then_else in
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
                      let uu____1273 =
                        let uu____1282 =
                          let uu____1285 =
                            let uu____1288 =
                              let uu____1297 =
                                let uu____1300 =
                                  let uu____1303 =
                                    let uu____1312 =
                                      let uu____1313 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1313 in
                                    [uu____1312] in
                                  FStar_Syntax_Util.mk_app l_and uu____1303 in
                                [uu____1300] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1297 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1288 in
                          let uu____1318 =
                            let uu____1323 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1323] in
                          uu____1285 :: uu____1318 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1282 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1273 in
                    let uu____1326 =
                      let uu____1327 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1327 in
                    FStar_Syntax_Util.abs uu____1326 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1339 = mk_lid "wp_assert" in
                    register env1 uu____1339 wp_assert in
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
                      let uu____1350 =
                        let uu____1359 =
                          let uu____1362 =
                            let uu____1365 =
                              let uu____1374 =
                                let uu____1377 =
                                  let uu____1380 =
                                    let uu____1389 =
                                      let uu____1390 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1390 in
                                    [uu____1389] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1380 in
                                [uu____1377] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1374 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1365 in
                          let uu____1395 =
                            let uu____1400 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1400] in
                          uu____1362 :: uu____1395 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1359 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1350 in
                    let uu____1403 =
                      let uu____1404 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1404 in
                    FStar_Syntax_Util.abs uu____1403 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1416 = mk_lid "wp_assume" in
                    register env1 uu____1416 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1425 =
                        let uu____1432 =
                          let uu____1433 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1433 in
                        [uu____1432] in
                      let uu____1434 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1425 uu____1434 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1441 =
                        let uu____1450 =
                          let uu____1453 =
                            let uu____1456 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1456 in
                          let uu____1465 =
                            let uu____1470 =
                              let uu____1473 =
                                let uu____1482 =
                                  let uu____1485 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1485] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1482 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1473 in
                            [uu____1470] in
                          uu____1453 :: uu____1465 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1450 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1441 in
                    let uu____1492 =
                      let uu____1493 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1493 in
                    FStar_Syntax_Util.abs uu____1492 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1505 = mk_lid "wp_close" in
                    register env1 uu____1505 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1515 =
                      let uu____1516 =
                        let uu____1517 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1517 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1516 in
                    FStar_Pervasives_Native.Some uu____1515 in
                  let mk_forall1 x body =
                    let uu____1529 =
                      let uu____1532 =
                        let uu____1533 =
                          let uu____1548 =
                            let uu____1551 =
                              let uu____1552 =
                                let uu____1553 =
                                  let uu____1554 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1554] in
                                FStar_Syntax_Util.abs uu____1553 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1552 in
                            [uu____1551] in
                          (FStar_Syntax_Util.tforall, uu____1548) in
                        FStar_Syntax_Syntax.Tm_app uu____1533 in
                      FStar_Syntax_Syntax.mk uu____1532 in
                    uu____1529 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1564 =
                      let uu____1565 = FStar_Syntax_Subst.compress t in
                      uu____1565.FStar_Syntax_Syntax.n in
                    match uu____1564 with
                    | FStar_Syntax_Syntax.Tm_type uu____1568 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1594  ->
                              match uu____1594 with
                              | (b,uu____1600) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1601 -> true in
                  let rec is_monotonic t =
                    let uu____1606 =
                      let uu____1607 = FStar_Syntax_Subst.compress t in
                      uu____1607.FStar_Syntax_Syntax.n in
                    match uu____1606 with
                    | FStar_Syntax_Syntax.Tm_type uu____1610 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1636  ->
                              match uu____1636 with
                              | (b,uu____1642) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1643 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1695 =
                      let uu____1696 = FStar_Syntax_Subst.compress t1 in
                      uu____1696.FStar_Syntax_Syntax.n in
                    match uu____1695 with
                    | FStar_Syntax_Syntax.Tm_type uu____1699 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1702);
                                      FStar_Syntax_Syntax.pos = uu____1703;
                                      FStar_Syntax_Syntax.vars = uu____1704;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1738 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1738
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1741 =
                              let uu____1744 =
                                let uu____1753 =
                                  let uu____1754 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1754 in
                                [uu____1753] in
                              FStar_Syntax_Util.mk_app x uu____1744 in
                            let uu____1755 =
                              let uu____1758 =
                                let uu____1767 =
                                  let uu____1768 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1768 in
                                [uu____1767] in
                              FStar_Syntax_Util.mk_app y uu____1758 in
                            mk_rel1 b uu____1741 uu____1755 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1773 =
                               let uu____1774 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1777 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1774 uu____1777 in
                             let uu____1780 =
                               let uu____1781 =
                                 let uu____1784 =
                                   let uu____1793 =
                                     let uu____1794 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1794 in
                                   [uu____1793] in
                                 FStar_Syntax_Util.mk_app x uu____1784 in
                               let uu____1795 =
                                 let uu____1798 =
                                   let uu____1807 =
                                     let uu____1808 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1808 in
                                   [uu____1807] in
                                 FStar_Syntax_Util.mk_app y uu____1798 in
                               mk_rel1 b uu____1781 uu____1795 in
                             FStar_Syntax_Util.mk_imp uu____1773 uu____1780 in
                           let uu____1809 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1809)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1812);
                                      FStar_Syntax_Syntax.pos = uu____1813;
                                      FStar_Syntax_Syntax.vars = uu____1814;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1848 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1848
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1851 =
                              let uu____1854 =
                                let uu____1863 =
                                  let uu____1864 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1864 in
                                [uu____1863] in
                              FStar_Syntax_Util.mk_app x uu____1854 in
                            let uu____1865 =
                              let uu____1868 =
                                let uu____1877 =
                                  let uu____1878 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1878 in
                                [uu____1877] in
                              FStar_Syntax_Util.mk_app y uu____1868 in
                            mk_rel1 b uu____1851 uu____1865 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1883 =
                               let uu____1884 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1887 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1884 uu____1887 in
                             let uu____1890 =
                               let uu____1891 =
                                 let uu____1894 =
                                   let uu____1903 =
                                     let uu____1904 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1904 in
                                   [uu____1903] in
                                 FStar_Syntax_Util.mk_app x uu____1894 in
                               let uu____1905 =
                                 let uu____1908 =
                                   let uu____1917 =
                                     let uu____1918 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1918 in
                                   [uu____1917] in
                                 FStar_Syntax_Util.mk_app y uu____1908 in
                               mk_rel1 b uu____1891 uu____1905 in
                             FStar_Syntax_Util.mk_imp uu____1883 uu____1890 in
                           let uu____1919 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1919)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___103_1950 = t1 in
                          let uu____1951 =
                            let uu____1952 =
                              let uu____1965 =
                                let uu____1966 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1966 in
                              ([binder], uu____1965) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1952 in
                          {
                            FStar_Syntax_Syntax.n = uu____1951;
                            FStar_Syntax_Syntax.pos =
                              (uu___103_1950.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___103_1950.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1981 ->
                        failwith "unhandled arrow"
                    | uu____1994 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____2009 =
                        let uu____2010 = FStar_Syntax_Subst.compress t1 in
                        uu____2010.FStar_Syntax_Syntax.n in
                      match uu____2009 with
                      | FStar_Syntax_Syntax.Tm_type uu____2013 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2036 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____2036
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2051 =
                                let uu____2052 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2052 i in
                              FStar_Syntax_Syntax.fvar uu____2051
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____2079 =
                            let uu____2086 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2100  ->
                                     match uu____2100 with
                                     | (t2,q) ->
                                         let uu____2107 = project i x in
                                         let uu____2108 = project i y in
                                         mk_stronger t2 uu____2107 uu____2108)
                                args in
                            match uu____2086 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____2079 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2135);
                                      FStar_Syntax_Syntax.pos = uu____2136;
                                      FStar_Syntax_Syntax.vars = uu____2137;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2175  ->
                                   match uu____2175 with
                                   | (bv,q) ->
                                       let uu____2182 =
                                         let uu____2183 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2183 in
                                       FStar_Syntax_Syntax.gen_bv uu____2182
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2190 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2190) bvs in
                          let body =
                            let uu____2192 = FStar_Syntax_Util.mk_app x args in
                            let uu____2193 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2192 uu____2193 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2200);
                                      FStar_Syntax_Syntax.pos = uu____2201;
                                      FStar_Syntax_Syntax.vars = uu____2202;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2240  ->
                                   match uu____2240 with
                                   | (bv,q) ->
                                       let uu____2247 =
                                         let uu____2248 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____2248 in
                                       FStar_Syntax_Syntax.gen_bv uu____2247
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2255 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____2255) bvs in
                          let body =
                            let uu____2257 = FStar_Syntax_Util.mk_app x args in
                            let uu____2258 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____2257 uu____2258 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2263 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____2265 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____2266 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____2267 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____2265 uu____2266 uu____2267 in
                    let uu____2268 =
                      let uu____2269 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____2269 in
                    FStar_Syntax_Util.abs uu____2268 body ret_tot_type in
                  let stronger1 =
                    let uu____2297 = mk_lid "stronger" in
                    register env1 uu____2297 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2303 = FStar_Util.prefix gamma in
                    match uu____2303 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____2348 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2348 in
                          let uu____2351 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____2351 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2361 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____2361 in
                              let guard_free1 =
                                let uu____2371 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____2371 in
                              let pat =
                                let uu____2375 =
                                  let uu____2384 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____2384] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2375 in
                              let pattern_guarded_body =
                                let uu____2388 =
                                  let uu____2389 =
                                    let uu____2396 =
                                      let uu____2397 =
                                        let uu____2408 =
                                          let uu____2411 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2411] in
                                        [uu____2408] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2397 in
                                    (body, uu____2396) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2389 in
                                mk1 uu____2388 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2416 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2420 =
                            let uu____2421 =
                              let uu____2422 =
                                let uu____2423 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2426 =
                                  let uu____2435 = args_of_binders1 wp_args in
                                  let uu____2438 =
                                    let uu____2441 =
                                      let uu____2442 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2442 in
                                    [uu____2441] in
                                  FStar_List.append uu____2435 uu____2438 in
                                FStar_Syntax_Util.mk_app uu____2423
                                  uu____2426 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2422 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2421 in
                          FStar_Syntax_Util.abs gamma uu____2420
                            ret_gtot_type in
                        let uu____2443 =
                          let uu____2444 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2444 in
                        FStar_Syntax_Util.abs uu____2443 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2456 = mk_lid "wp_ite" in
                    register env1 uu____2456 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____2462 = FStar_Util.prefix gamma in
                    match uu____2462 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2505 =
                            let uu____2506 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2509 =
                              let uu____2518 =
                                let uu____2519 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2519 in
                              [uu____2518] in
                            FStar_Syntax_Util.mk_app uu____2506 uu____2509 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2505 in
                        let uu____2520 =
                          let uu____2521 =
                            let uu____2528 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2528 gamma in
                          FStar_List.append binders uu____2521 in
                        FStar_Syntax_Util.abs uu____2520 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2544 = mk_lid "null_wp" in
                    register env1 uu____2544 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2553 =
                        let uu____2562 =
                          let uu____2565 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2566 =
                            let uu____2569 =
                              let uu____2572 =
                                let uu____2581 =
                                  let uu____2582 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2582 in
                                [uu____2581] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2572 in
                            let uu____2583 =
                              let uu____2588 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2588] in
                            uu____2569 :: uu____2583 in
                          uu____2565 :: uu____2566 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2562 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2553 in
                    let uu____2591 =
                      let uu____2592 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2592 in
                    FStar_Syntax_Util.abs uu____2591 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2604 = mk_lid "wp_trivial" in
                    register env1 uu____2604 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2609 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2609
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2614 =
                      let uu____2617 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2617 in
                    let uu____2624 =
                      let uu___104_2625 = ed in
                      let uu____2626 =
                        let uu____2627 = c wp_if_then_else2 in
                        ([], uu____2627) in
                      let uu____2630 =
                        let uu____2631 = c wp_ite2 in ([], uu____2631) in
                      let uu____2634 =
                        let uu____2635 = c stronger2 in ([], uu____2635) in
                      let uu____2638 =
                        let uu____2639 = c wp_close2 in ([], uu____2639) in
                      let uu____2642 =
                        let uu____2643 = c wp_assert2 in ([], uu____2643) in
                      let uu____2646 =
                        let uu____2647 = c wp_assume2 in ([], uu____2647) in
                      let uu____2650 =
                        let uu____2651 = c null_wp2 in ([], uu____2651) in
                      let uu____2654 =
                        let uu____2655 = c wp_trivial2 in ([], uu____2655) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___104_2625.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___104_2625.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___104_2625.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___104_2625.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___104_2625.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___104_2625.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___104_2625.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2626;
                        FStar_Syntax_Syntax.ite_wp = uu____2630;
                        FStar_Syntax_Syntax.stronger = uu____2634;
                        FStar_Syntax_Syntax.close_wp = uu____2638;
                        FStar_Syntax_Syntax.assert_p = uu____2642;
                        FStar_Syntax_Syntax.assume_p = uu____2646;
                        FStar_Syntax_Syntax.null_wp = uu____2650;
                        FStar_Syntax_Syntax.trivial = uu____2654;
                        FStar_Syntax_Syntax.repr =
                          (uu___104_2625.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___104_2625.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___104_2625.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___104_2625.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2614, uu____2624)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___105_2672 = dmff_env in
      {
        env = env';
        subst = (uu___105_2672.subst);
        tc_const = (uu___105_2672.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2686 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2700 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___91_2712  ->
    match uu___91_2712 with
    | FStar_Syntax_Syntax.Total (t,uu____2714) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___90_2727  ->
                match uu___90_2727 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2728 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2730 =
          let uu____2731 =
            let uu____2732 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2732 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2731 in
        failwith uu____2730
    | FStar_Syntax_Syntax.GTotal uu____2733 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___92_2745  ->
    match uu___92_2745 with
    | N t ->
        let uu____2747 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2747
    | M t ->
        let uu____2749 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2749
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2754,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2756;
                      FStar_Syntax_Syntax.vars = uu____2757;_})
        -> nm_of_comp n2
    | uu____2774 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____2783 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____2783 with | M uu____2784 -> true | N uu____2785 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2790 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2801 =
        let uu____2808 =
          let uu____2809 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2809 in
        [uu____2808] in
      let uu____2810 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2801 uu____2810 in
    let uu____2813 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2813
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
          (let uu____2850 =
             let uu____2863 =
               let uu____2870 =
                 let uu____2875 =
                   let uu____2876 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2876 in
                 let uu____2877 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2875, uu____2877) in
               [uu____2870] in
             let uu____2886 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2863, uu____2886) in
           FStar_Syntax_Syntax.Tm_arrow uu____2850)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2914) ->
          let binders1 =
            FStar_List.map
              (fun uu____2950  ->
                 match uu____2950 with
                 | (bv,aqual) ->
                     let uu____2961 =
                       let uu___106_2962 = bv in
                       let uu____2963 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_2962.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_2962.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2963
                       } in
                     (uu____2961, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2966,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2968);
                             FStar_Syntax_Syntax.pos = uu____2969;
                             FStar_Syntax_Syntax.vars = uu____2970;_})
               ->
               let uu____2995 =
                 let uu____2996 =
                   let uu____3009 =
                     let uu____3010 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____3010 in
                   (binders1, uu____3009) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2996 in
               mk1 uu____2995
           | uu____3017 ->
               let uu____3018 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____3018 with
                | N hn ->
                    let uu____3020 =
                      let uu____3021 =
                        let uu____3034 =
                          let uu____3035 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____3035 in
                        (binders1, uu____3034) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3021 in
                    mk1 uu____3020
                | M a ->
                    let uu____3043 =
                      let uu____3044 =
                        let uu____3057 =
                          let uu____3064 =
                            let uu____3071 =
                              let uu____3076 =
                                let uu____3077 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____3077 in
                              let uu____3078 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____3076, uu____3078) in
                            [uu____3071] in
                          FStar_List.append binders1 uu____3064 in
                        let uu____3091 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____3057, uu____3091) in
                      FStar_Syntax_Syntax.Tm_arrow uu____3044 in
                    mk1 uu____3043))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3157 = f x in
                    FStar_Util.string_builder_append strb uu____3157);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3164 = f x1 in
                         FStar_Util.string_builder_append strb uu____3164))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____3166 = FStar_Syntax_Print.term_to_string t2 in
            let uu____3167 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____3166 uu____3167 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3175 =
              let uu____3176 = FStar_Syntax_Subst.compress ty in
              uu____3176.FStar_Syntax_Syntax.n in
            match uu____3175 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3197 =
                  let uu____3198 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____3198 in
                if uu____3197
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3224 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____3224 s in
                       let uu____3227 =
                         let uu____3228 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____3228 in
                       if uu____3227
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____3231 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____3231 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3253  ->
                                  match uu____3253 with
                                  | (bv,uu____3263) ->
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
            | uu____3277 ->
                ((let uu____3279 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____3279);
                 false) in
          let rec is_valid_application head2 =
            let uu____3284 =
              let uu____3285 = FStar_Syntax_Subst.compress head2 in
              uu____3285.FStar_Syntax_Syntax.n in
            match uu____3284 with
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
                  (let uu____3290 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____3290)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3292 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____3292 with
                 | ((uu____3301,ty),uu____3303) ->
                     let uu____3308 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____3308
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3316 -> true
                        | uu____3331 ->
                            ((let uu____3333 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____3333);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3335 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3336 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3338) ->
                is_valid_application t2
            | uu____3343 -> false in
          let uu____3344 = is_valid_application head1 in
          if uu____3344
          then
            let uu____3345 =
              let uu____3346 =
                let uu____3361 =
                  FStar_List.map
                    (fun uu____3382  ->
                       match uu____3382 with
                       | (t2,qual) ->
                           let uu____3399 = star_type' env t2 in
                           (uu____3399, qual)) args in
                (head1, uu____3361) in
              FStar_Syntax_Syntax.Tm_app uu____3346 in
            mk1 uu____3345
          else
            (let uu____3409 =
               let uu____3410 =
                 let uu____3411 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3411 in
               FStar_Errors.Err uu____3410 in
             raise uu____3409)
      | FStar_Syntax_Syntax.Tm_bvar uu____3412 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3413 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3414 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3415 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3439 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____3439 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___109_3447 = env in
                 let uu____3448 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____3448;
                   subst = (uu___109_3447.subst);
                   tc_const = (uu___109_3447.tc_const)
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
               ((let uu___110_3468 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___110_3468.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___110_3468.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3475 =
            let uu____3476 =
              let uu____3483 = star_type' env t2 in (uu____3483, m) in
            FStar_Syntax_Syntax.Tm_meta uu____3476 in
          mk1 uu____3475
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3531 =
            let uu____3532 =
              let uu____3559 = star_type' env e in
              let uu____3560 =
                let uu____3575 =
                  let uu____3582 = star_type' env t2 in
                  FStar_Util.Inl uu____3582 in
                (uu____3575, FStar_Pervasives_Native.None) in
              (uu____3559, uu____3560, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____3532 in
          mk1 uu____3531
      | FStar_Syntax_Syntax.Tm_ascribed uu____3613 ->
          let uu____3640 =
            let uu____3641 =
              let uu____3642 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____3642 in
            FStar_Errors.Err uu____3641 in
          raise uu____3640
      | FStar_Syntax_Syntax.Tm_refine uu____3643 ->
          let uu____3650 =
            let uu____3651 =
              let uu____3652 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3652 in
            FStar_Errors.Err uu____3651 in
          raise uu____3650
      | FStar_Syntax_Syntax.Tm_uinst uu____3653 ->
          let uu____3660 =
            let uu____3661 =
              let uu____3662 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3662 in
            FStar_Errors.Err uu____3661 in
          raise uu____3660
      | FStar_Syntax_Syntax.Tm_constant uu____3663 ->
          let uu____3664 =
            let uu____3665 =
              let uu____3666 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3666 in
            FStar_Errors.Err uu____3665 in
          raise uu____3664
      | FStar_Syntax_Syntax.Tm_match uu____3667 ->
          let uu____3690 =
            let uu____3691 =
              let uu____3692 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3692 in
            FStar_Errors.Err uu____3691 in
          raise uu____3690
      | FStar_Syntax_Syntax.Tm_let uu____3693 ->
          let uu____3706 =
            let uu____3707 =
              let uu____3708 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____3708 in
            FStar_Errors.Err uu____3707 in
          raise uu____3706
      | FStar_Syntax_Syntax.Tm_uvar uu____3709 ->
          let uu____3726 =
            let uu____3727 =
              let uu____3728 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____3728 in
            FStar_Errors.Err uu____3727 in
          raise uu____3726
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____3729 =
            let uu____3730 =
              let uu____3731 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____3731 in
            FStar_Errors.Err uu____3730 in
          raise uu____3729
      | FStar_Syntax_Syntax.Tm_delayed uu____3732 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___94_3762  ->
    match uu___94_3762 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___93_3769  ->
                match uu___93_3769 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____3770 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3775 =
      let uu____3776 = FStar_Syntax_Subst.compress t in
      uu____3776.FStar_Syntax_Syntax.n in
    match uu____3775 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3802 =
            let uu____3803 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____3803 in
          is_C uu____3802 in
        if r
        then
          ((let uu____3819 =
              let uu____3820 =
                FStar_List.for_all
                  (fun uu____3828  ->
                     match uu____3828 with | (h,uu____3834) -> is_C h) args in
              Prims.op_Negation uu____3820 in
            if uu____3819 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3838 =
              let uu____3839 =
                FStar_List.for_all
                  (fun uu____3848  ->
                     match uu____3848 with
                     | (h,uu____3854) ->
                         let uu____3855 = is_C h in
                         Prims.op_Negation uu____3855) args in
              Prims.op_Negation uu____3839 in
            if uu____3838 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3875 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3875 with
         | M t1 ->
             ((let uu____3878 = is_C t1 in
               if uu____3878 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3882) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3888) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3894,uu____3895) -> is_C t1
    | uu____3936 -> false
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
          let uu____3962 =
            let uu____3963 =
              let uu____3978 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3979 =
                let uu____3986 =
                  let uu____3991 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3991) in
                [uu____3986] in
              (uu____3978, uu____3979) in
            FStar_Syntax_Syntax.Tm_app uu____3963 in
          mk1 uu____3962 in
        let uu____4006 =
          let uu____4007 = FStar_Syntax_Syntax.mk_binder p in [uu____4007] in
        FStar_Syntax_Util.abs uu____4006 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___95_4011  ->
    match uu___95_4011 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4012 -> false
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
        let return_if uu____4187 =
          match uu____4187 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4214 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4216 =
                       let uu____4217 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____4217 in
                     Prims.op_Negation uu____4216) in
                if uu____4214
                then
                  let uu____4218 =
                    let uu____4219 =
                      let uu____4220 = FStar_Syntax_Print.term_to_string e in
                      let uu____4221 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____4222 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4220 uu____4221 uu____4222 in
                    FStar_Errors.Err uu____4219 in
                  raise uu____4218
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4239 = mk_return env t1 s_e in
                     ((M t1), uu____4239, u_e)))
               | (M t1,N t2) ->
                   let uu____4242 =
                     let uu____4243 =
                       let uu____4244 = FStar_Syntax_Print.term_to_string e in
                       let uu____4245 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____4246 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4244 uu____4245 uu____4246 in
                     FStar_Errors.Err uu____4243 in
                   raise uu____4242) in
        let ensure_m env1 e2 =
          let strip_m uu___96_4287 =
            match uu___96_4287 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4303 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____4323 =
                let uu____4324 =
                  let uu____4329 =
                    let uu____4330 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____4330 in
                  (uu____4329, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____4324 in
              raise uu____4323
          | M uu____4337 ->
              let uu____4338 = check env1 e2 context_nm in strip_m uu____4338 in
        let uu____4345 =
          let uu____4346 = FStar_Syntax_Subst.compress e in
          uu____4346.FStar_Syntax_Syntax.n in
        match uu____4345 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4355 ->
            let uu____4356 = infer env e in return_if uu____4356
        | FStar_Syntax_Syntax.Tm_name uu____4363 ->
            let uu____4364 = infer env e in return_if uu____4364
        | FStar_Syntax_Syntax.Tm_fvar uu____4371 ->
            let uu____4372 = infer env e in return_if uu____4372
        | FStar_Syntax_Syntax.Tm_abs uu____4379 ->
            let uu____4396 = infer env e in return_if uu____4396
        | FStar_Syntax_Syntax.Tm_constant uu____4403 ->
            let uu____4404 = infer env e in return_if uu____4404
        | FStar_Syntax_Syntax.Tm_app uu____4411 ->
            let uu____4426 = infer env e in return_if uu____4426
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4494) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4500) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4506,uu____4507) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4548 ->
            let uu____4561 =
              let uu____4562 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4562 in
            failwith uu____4561
        | FStar_Syntax_Syntax.Tm_type uu____4569 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4576 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4595 ->
            let uu____4602 =
              let uu____4603 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4603 in
            failwith uu____4602
        | FStar_Syntax_Syntax.Tm_uvar uu____4610 ->
            let uu____4627 =
              let uu____4628 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4628 in
            failwith uu____4627
        | FStar_Syntax_Syntax.Tm_delayed uu____4635 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4666 =
              let uu____4667 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4667 in
            failwith uu____4666
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
      let uu____4691 =
        let uu____4692 = FStar_Syntax_Subst.compress e in
        uu____4692.FStar_Syntax_Syntax.n in
      match uu____4691 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____4751;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____4752;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____4758 =
                  let uu___111_4759 = rc in
                  let uu____4760 =
                    let uu____4765 =
                      let uu____4766 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____4766 in
                    FStar_Pervasives_Native.Some uu____4765 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___111_4759.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____4760;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___111_4759.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____4758 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___112_4776 = env in
            let uu____4777 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____4777;
              subst = (uu___112_4776.subst);
              tc_const = (uu___112_4776.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____4797  ->
                 match uu____4797 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_4810 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_4810.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_4810.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____4811 =
            FStar_List.fold_left
              (fun uu____4840  ->
                 fun uu____4841  ->
                   match (uu____4840, uu____4841) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____4889 = is_C c in
                       if uu____4889
                       then
                         let xw =
                           let uu____4897 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____4897 in
                         let x =
                           let uu___114_4899 = bv in
                           let uu____4900 =
                             let uu____4903 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____4903 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_4899.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_4899.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____4900
                           } in
                         let env3 =
                           let uu___115_4905 = env2 in
                           let uu____4906 =
                             let uu____4909 =
                               let uu____4910 =
                                 let uu____4917 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____4917) in
                               FStar_Syntax_Syntax.NT uu____4910 in
                             uu____4909 :: (env2.subst) in
                           {
                             env = (uu___115_4905.env);
                             subst = uu____4906;
                             tc_const = (uu___115_4905.tc_const)
                           } in
                         let uu____4918 =
                           let uu____4921 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____4922 =
                             let uu____4925 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____4925 :: acc in
                           uu____4921 :: uu____4922 in
                         (env3, uu____4918)
                       else
                         (let x =
                            let uu___116_4930 = bv in
                            let uu____4931 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_4930.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_4930.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____4931
                            } in
                          let uu____4934 =
                            let uu____4937 = FStar_Syntax_Syntax.mk_binder x in
                            uu____4937 :: acc in
                          (env2, uu____4934))) (env1, []) binders1 in
          (match uu____4811 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____4957 =
                 let check_what =
                   let uu____4975 = is_monadic rc_opt1 in
                   if uu____4975 then check_m else check_n in
                 let uu____4987 = check_what env2 body1 in
                 match uu____4987 with
                 | (t,s_body,u_body) ->
                     let uu____5003 =
                       let uu____5004 =
                         let uu____5005 = is_monadic rc_opt1 in
                         if uu____5005 then M t else N t in
                       comp_of_nm uu____5004 in
                     (uu____5003, s_body, u_body) in
               (match uu____4957 with
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
                                 let uu____5030 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___97_5034  ->
                                           match uu___97_5034 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5035 -> false)) in
                                 if uu____5030
                                 then
                                   let uu____5036 =
                                     FStar_List.filter
                                       (fun uu___98_5040  ->
                                          match uu___98_5040 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5041 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5036
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5050 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___99_5054  ->
                                         match uu___99_5054 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5055 -> false)) in
                               if uu____5050
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___100_5062  ->
                                        match uu___100_5062 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5063 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____5064 =
                                   let uu____5065 =
                                     let uu____5070 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____5070 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5065 flags in
                                 FStar_Pervasives_Native.Some uu____5064
                               else
                                 (let uu____5072 =
                                    let uu___117_5073 = rc in
                                    let uu____5074 =
                                      let uu____5079 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____5079 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_5073.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5074;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_5073.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____5072)) in
                    let uu____5080 =
                      let comp1 =
                        let uu____5090 = is_monadic rc_opt1 in
                        let uu____5091 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5090 uu____5091 in
                      let uu____5092 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____5092,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____5080 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____5134 =
                             let uu____5135 =
                               let uu____5152 =
                                 let uu____5155 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____5155 s_rc_opt in
                               (s_binders1, s_body1, uu____5152) in
                             FStar_Syntax_Syntax.Tm_abs uu____5135 in
                           mk1 uu____5134 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____5165 =
                             let uu____5166 =
                               let uu____5183 =
                                 let uu____5186 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____5186 u_rc_opt in
                               (u_binders2, u_body2, uu____5183) in
                             FStar_Syntax_Syntax.Tm_abs uu____5166 in
                           mk1 uu____5165 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5196;_};
            FStar_Syntax_Syntax.fv_delta = uu____5197;
            FStar_Syntax_Syntax.fv_qual = uu____5198;_}
          ->
          let uu____5201 =
            let uu____5206 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5206 in
          (match uu____5201 with
           | (uu____5237,t) ->
               let uu____5239 = let uu____5240 = normalize1 t in N uu____5240 in
               (uu____5239, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____5263 = check_n env head1 in
          (match uu____5263 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____5283 =
                   let uu____5284 = FStar_Syntax_Subst.compress t in
                   uu____5284.FStar_Syntax_Syntax.n in
                 match uu____5283 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____5287 -> true
                 | uu____5300 -> false in
               let rec flatten1 t =
                 let uu____5317 =
                   let uu____5318 = FStar_Syntax_Subst.compress t in
                   uu____5318.FStar_Syntax_Syntax.n in
                 match uu____5317 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____5335);
                                FStar_Syntax_Syntax.pos = uu____5336;
                                FStar_Syntax_Syntax.vars = uu____5337;_})
                     when is_arrow t1 ->
                     let uu____5362 = flatten1 t1 in
                     (match uu____5362 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5444,uu____5445)
                     -> flatten1 e1
                 | uu____5486 ->
                     let uu____5487 =
                       let uu____5488 =
                         let uu____5489 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____5489 in
                       FStar_Errors.Err uu____5488 in
                     raise uu____5487 in
               let uu____5502 = flatten1 t_head in
               (match uu____5502 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____5562 =
                          let uu____5563 =
                            let uu____5564 = FStar_Util.string_of_int n1 in
                            let uu____5571 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____5582 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____5564 uu____5571 uu____5582 in
                          FStar_Errors.Err uu____5563 in
                        raise uu____5562)
                     else ();
                     (let uu____5590 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____5590 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____5631 args1 =
                            match uu____5631 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____5705 =
                                       let uu____5706 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____5706.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____5705
                                 | (binders3,[]) ->
                                     let uu____5736 =
                                       let uu____5737 =
                                         let uu____5740 =
                                           let uu____5741 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____5741 in
                                         FStar_Syntax_Subst.compress
                                           uu____5740 in
                                       uu____5737.FStar_Syntax_Syntax.n in
                                     (match uu____5736 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____5766 =
                                            let uu____5767 =
                                              let uu____5768 =
                                                let uu____5781 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____5781) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____5768 in
                                            mk1 uu____5767 in
                                          N uu____5766
                                      | uu____5788 -> failwith "wat?")
                                 | ([],uu____5789::uu____5790) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____5830)::binders3,(arg,uu____5833)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____5886 = FStar_List.splitAt n' binders1 in
                          (match uu____5886 with
                           | (binders2,uu____5918) ->
                               let uu____5943 =
                                 let uu____5962 =
                                   FStar_List.map2
                                     (fun uu____6010  ->
                                        fun uu____6011  ->
                                          match (uu____6010, uu____6011) with
                                          | ((bv,uu____6043),(arg,q)) ->
                                              let uu____6054 =
                                                let uu____6055 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____6055.FStar_Syntax_Syntax.n in
                                              (match uu____6054 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____6072 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____6096 ->
                                                   let uu____6097 =
                                                     check_n env arg in
                                                   (match uu____6097 with
                                                    | (uu____6118,s_arg,u_arg)
                                                        ->
                                                        let uu____6121 =
                                                          let uu____6128 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____6128
                                                          then
                                                            let uu____6135 =
                                                              let uu____6140
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____6140, q) in
                                                            [uu____6135;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____6121))))
                                     binders2 args in
                                 FStar_List.split uu____5962 in
                               (match uu____5943 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____6229 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____6238 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____6229, uu____6238)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____6304) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____6310) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6316,uu____6317) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____6359 = let uu____6360 = env.tc_const c in N uu____6360 in
          (uu____6359, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____6361 ->
          let uu____6374 =
            let uu____6375 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____6375 in
          failwith uu____6374
      | FStar_Syntax_Syntax.Tm_type uu____6382 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____6389 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____6408 ->
          let uu____6415 =
            let uu____6416 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____6416 in
          failwith uu____6415
      | FStar_Syntax_Syntax.Tm_uvar uu____6423 ->
          let uu____6440 =
            let uu____6441 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____6441 in
          failwith uu____6440
      | FStar_Syntax_Syntax.Tm_delayed uu____6448 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____6479 =
            let uu____6480 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____6480 in
          failwith uu____6479
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
          let uu____6525 = check_n env e0 in
          match uu____6525 with
          | (uu____6538,s_e0,u_e0) ->
              let uu____6541 =
                let uu____6570 =
                  FStar_List.map
                    (fun b  ->
                       let uu____6631 = FStar_Syntax_Subst.open_branch b in
                       match uu____6631 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___118_6673 = env in
                             let uu____6674 =
                               let uu____6675 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____6675 in
                             {
                               env = uu____6674;
                               subst = (uu___118_6673.subst);
                               tc_const = (uu___118_6673.tc_const)
                             } in
                           let uu____6678 = f env1 body in
                           (match uu____6678 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____6750 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____6570 in
              (match uu____6541 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____6852 = FStar_List.hd nms in
                     match uu____6852 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___101_6858  ->
                          match uu___101_6858 with
                          | M uu____6859 -> true
                          | uu____6860 -> false) nms in
                   let uu____6861 =
                     let uu____6898 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____6988  ->
                              match uu____6988 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____7165 =
                                         check env original_body (M t2) in
                                       (match uu____7165 with
                                        | (uu____7202,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____7241,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____6898 in
                   (match uu____6861 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____7425  ->
                                 match uu____7425 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____7476 =
                                         let uu____7477 =
                                           let uu____7492 =
                                             let uu____7499 =
                                               let uu____7504 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____7505 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____7504, uu____7505) in
                                             [uu____7499] in
                                           (s_body, uu____7492) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____7477 in
                                       mk1 uu____7476 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____7537 =
                              let uu____7538 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____7538] in
                            let uu____7539 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____7537 uu____7539
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____7545 =
                              let uu____7552 =
                                let uu____7553 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____7553 in
                              [uu____7552] in
                            let uu____7554 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____7545 uu____7554 in
                          let uu____7557 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____7596 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____7557, uu____7596)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____7613 =
                             let uu____7616 =
                               let uu____7617 =
                                 let uu____7644 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____7644,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____7617 in
                             mk1 uu____7616 in
                           let uu____7681 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____7613, uu____7681))))
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
              let uu____7728 = FStar_Syntax_Syntax.mk_binder x in
              [uu____7728] in
            let uu____7729 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____7729 with
            | (x_binders1,e21) ->
                let uu____7742 = infer env e1 in
                (match uu____7742 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____7759 = is_C t1 in
                       if uu____7759
                       then
                         let uu___119_7760 = binding in
                         let uu____7761 =
                           let uu____7764 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____7764 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_7760.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_7760.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____7761;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_7760.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_7760.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_7767 = env in
                       let uu____7768 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_7770 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_7770.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_7770.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____7768;
                         subst = (uu___120_7767.subst);
                         tc_const = (uu___120_7767.tc_const)
                       } in
                     let uu____7771 = proceed env1 e21 in
                     (match uu____7771 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_7788 = binding in
                            let uu____7789 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_7788.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_7788.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____7789;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_7788.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_7788.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____7792 =
                            let uu____7795 =
                              let uu____7796 =
                                let uu____7809 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_7819 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_7819.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_7819.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_7819.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_7819.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____7809) in
                              FStar_Syntax_Syntax.Tm_let uu____7796 in
                            mk1 uu____7795 in
                          let uu____7820 =
                            let uu____7823 =
                              let uu____7824 =
                                let uu____7837 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_7847 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_7847.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_7847.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_7847.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_7847.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____7837) in
                              FStar_Syntax_Syntax.Tm_let uu____7824 in
                            mk1 uu____7823 in
                          (nm_rec, uu____7792, uu____7820))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_7856 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_7856.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_7856.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_7856.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_7858 = env in
                       let uu____7859 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_7861 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_7861.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_7861.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____7859;
                         subst = (uu___126_7858.subst);
                         tc_const = (uu___126_7858.tc_const)
                       } in
                     let uu____7862 = ensure_m env1 e21 in
                     (match uu____7862 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____7885 =
                              let uu____7886 =
                                let uu____7901 =
                                  let uu____7908 =
                                    let uu____7913 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____7914 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____7913, uu____7914) in
                                  [uu____7908] in
                                (s_e2, uu____7901) in
                              FStar_Syntax_Syntax.Tm_app uu____7886 in
                            mk1 uu____7885 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____7933 =
                              let uu____7934 =
                                let uu____7949 =
                                  let uu____7956 =
                                    let uu____7961 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____7961) in
                                  [uu____7956] in
                                (s_e1, uu____7949) in
                              FStar_Syntax_Syntax.Tm_app uu____7934 in
                            mk1 uu____7933 in
                          let uu____7976 =
                            let uu____7977 =
                              let uu____7978 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____7978] in
                            FStar_Syntax_Util.abs uu____7977 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____7979 =
                            let uu____7982 =
                              let uu____7983 =
                                let uu____7996 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_8006 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_8006.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_8006.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_8006.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_8006.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____7996) in
                              FStar_Syntax_Syntax.Tm_let uu____7983 in
                            mk1 uu____7982 in
                          ((M t2), uu____7976, uu____7979)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8018 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____8018 in
      let uu____8019 = check env e mn in
      match uu____8019 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8035 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____8057 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____8057 in
      let uu____8058 = check env e mn in
      match uu____8058 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____8074 -> failwith "[check_m]: impossible"
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
        (let uu____8104 =
           let uu____8105 = is_C c in Prims.op_Negation uu____8105 in
         if uu____8104 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____8113 =
           let uu____8114 = FStar_Syntax_Subst.compress c in
           uu____8114.FStar_Syntax_Syntax.n in
         match uu____8113 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____8139 = FStar_Syntax_Util.head_and_args wp in
             (match uu____8139 with
              | (wp_head,wp_args) ->
                  ((let uu____8177 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____8191 =
                           let uu____8192 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____8192 in
                         Prims.op_Negation uu____8191) in
                    if uu____8177 then failwith "mismatch" else ());
                   (let uu____8200 =
                      let uu____8201 =
                        let uu____8216 =
                          FStar_List.map2
                            (fun uu____8244  ->
                               fun uu____8245  ->
                                 match (uu____8244, uu____8245) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____8282 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____8282
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____8285 = print_implicit q in
                                         let uu____8286 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____8285 uu____8286)
                                      else ();
                                      (let uu____8288 =
                                         trans_F_ env arg wp_arg in
                                       (uu____8288, q)))) args wp_args in
                        (head1, uu____8216) in
                      FStar_Syntax_Syntax.Tm_app uu____8201 in
                    mk1 uu____8200)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____8322 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____8322 with
              | (binders_orig,comp1) ->
                  let uu____8329 =
                    let uu____8344 =
                      FStar_List.map
                        (fun uu____8378  ->
                           match uu____8378 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____8398 = is_C h in
                               if uu____8398
                               then
                                 let w' =
                                   let uu____8410 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____8410 in
                                 let uu____8411 =
                                   let uu____8418 =
                                     let uu____8425 =
                                       let uu____8430 =
                                         let uu____8431 =
                                           let uu____8432 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____8432 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____8431 in
                                       (uu____8430, q) in
                                     [uu____8425] in
                                   (w', q) :: uu____8418 in
                                 (w', uu____8411)
                               else
                                 (let x =
                                    let uu____8453 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____8453 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____8344 in
                  (match uu____8329 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____8508 =
                           let uu____8511 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____8511 in
                         FStar_Syntax_Subst.subst_comp uu____8508 comp1 in
                       let app =
                         let uu____8515 =
                           let uu____8516 =
                             let uu____8531 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____8546 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____8547 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____8546, uu____8547)) bvs in
                             (wp, uu____8531) in
                           FStar_Syntax_Syntax.Tm_app uu____8516 in
                         mk1 uu____8515 in
                       let comp3 =
                         let uu____8555 = type_of_comp comp2 in
                         let uu____8556 = is_monadic_comp comp2 in
                         trans_G env uu____8555 uu____8556 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____8558,uu____8559) ->
             trans_F_ env e wp
         | uu____8600 -> failwith "impossible trans_F_")
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
            let uu____8605 =
              let uu____8606 = star_type' env h in
              let uu____8609 =
                let uu____8618 =
                  let uu____8623 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____8623) in
                [uu____8618] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____8606;
                FStar_Syntax_Syntax.effect_args = uu____8609;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____8605
          else
            (let uu____8633 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____8633)
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
    fun t  -> let uu____8648 = n env.env t in star_type' env uu____8648
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____8665 = n env.env t in check_n env uu____8665
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____8678 = n env.env c in
        let uu____8679 = n env.env wp in trans_F_ env uu____8678 uu____8679