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
              let uu___102_94 = a in
              let uu____95 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___102_94.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___102_94.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____95
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____103 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____103
             then
               (d "Elaborating extra WP combinators";
                (let uu____105 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____105))
             else ());
            (let rec collect_binders t =
               let uu____114 =
                 let uu____115 =
                   let uu____118 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____118 in
                 uu____115.FStar_Syntax_Syntax.n in
               match uu____114 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____140) -> t1
                     | uu____147 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____150 = collect_binders rest in
                   FStar_List.append bs uu____150
               | FStar_Syntax_Syntax.Tm_type uu____156 -> []
               | uu____159 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____171 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____171 FStar_Syntax_Util.name_binders in
             (let uu____182 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____182
              then
                let uu____183 =
                  let uu____184 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____184 in
                d uu____183
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____212 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____212 with
                | (sigelt,fv) ->
                    ((let uu____218 =
                        let uu____220 = FStar_ST.read sigelts in sigelt ::
                          uu____220 in
                      FStar_ST.write sigelts uu____218);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____245  ->
                     match uu____245 with
                     | (t,b) ->
                         let uu____252 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____252)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____271 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____271)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____286 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____286) in
              let uu____287 =
                let uu____299 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____319 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____319 in
                    let uu____322 =
                      let uu____323 =
                        let uu____327 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____328 =
                          let uu____330 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____330] in
                        uu____327 :: uu____328 in
                      FStar_List.append binders uu____323 in
                    FStar_Syntax_Util.abs uu____322 body
                      FStar_Pervasives_Native.None in
                  let uu____333 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____334 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____333, uu____334) in
                match uu____299 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____365 =
                        let uu____366 =
                          let uu____376 =
                            let uu____380 =
                              FStar_List.map
                                (fun uu____393  ->
                                   match uu____393 with
                                   | (bv,uu____399) ->
                                       let uu____400 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____401 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____400, uu____401)) binders in
                            let uu____402 =
                              let uu____406 =
                                let uu____409 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____410 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____409, uu____410) in
                              let uu____411 =
                                let uu____415 =
                                  let uu____418 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____418) in
                                [uu____415] in
                              uu____406 :: uu____411 in
                            FStar_List.append uu____380 uu____402 in
                          (fv, uu____376) in
                        FStar_Syntax_Syntax.Tm_app uu____366 in
                      mk1 uu____365 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____287 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____464 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____464 in
                    let ret1 =
                      let uu____467 =
                        let uu____468 =
                          let uu____471 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____471 in
                        FStar_Syntax_Util.residual_tot uu____468 in
                      FStar_Pervasives_Native.Some uu____467 in
                    let body =
                      let uu____473 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____473 ret1 in
                    let uu____474 =
                      let uu____475 = mk_all_implicit binders in
                      let uu____479 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____475 uu____479 in
                    FStar_Syntax_Util.abs uu____474 body ret1 in
                  let c_pure1 =
                    let uu____494 = mk_lid "pure" in
                    register env1 uu____494 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____499 =
                        let uu____500 =
                          let uu____501 =
                            let uu____505 =
                              let uu____506 =
                                let uu____507 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____507 in
                              FStar_Syntax_Syntax.mk_binder uu____506 in
                            [uu____505] in
                          let uu____508 =
                            let uu____511 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____511 in
                          FStar_Syntax_Util.arrow uu____501 uu____508 in
                        mk_gctx uu____500 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____499 in
                    let r =
                      let uu____513 =
                        let uu____514 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____514 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____513 in
                    let ret1 =
                      let uu____517 =
                        let uu____518 =
                          let uu____521 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____521 in
                        FStar_Syntax_Util.residual_tot uu____518 in
                      FStar_Pervasives_Native.Some uu____517 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____528 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____531 =
                          let uu____537 =
                            let uu____539 =
                              let uu____540 =
                                let uu____541 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____541
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____540 in
                            [uu____539] in
                          FStar_List.append gamma_as_args uu____537 in
                        FStar_Syntax_Util.mk_app uu____528 uu____531 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____544 =
                      let uu____545 = mk_all_implicit binders in
                      let uu____549 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____545 uu____549 in
                    FStar_Syntax_Util.abs uu____544 outer_body ret1 in
                  let c_app1 =
                    let uu____568 = mk_lid "app" in
                    register env1 uu____568 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____575 =
                        let uu____579 =
                          let uu____580 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____580 in
                        [uu____579] in
                      let uu____581 =
                        let uu____584 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____584 in
                      FStar_Syntax_Util.arrow uu____575 uu____581 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____587 =
                        let uu____588 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____588 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____587 in
                    let ret1 =
                      let uu____591 =
                        let uu____592 =
                          let uu____595 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____595 in
                        FStar_Syntax_Util.residual_tot uu____592 in
                      FStar_Pervasives_Native.Some uu____591 in
                    let uu____596 =
                      let uu____597 = mk_all_implicit binders in
                      let uu____601 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____597 uu____601 in
                    let uu____619 =
                      let uu____620 =
                        let uu____626 =
                          let uu____628 =
                            let uu____631 =
                              let uu____637 =
                                let uu____639 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____639] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____637 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____631 in
                          let uu____640 =
                            let uu____644 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____644] in
                          uu____628 :: uu____640 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____626 in
                      FStar_Syntax_Util.mk_app c_app1 uu____620 in
                    FStar_Syntax_Util.abs uu____596 uu____619 ret1 in
                  let c_lift11 =
                    let uu____648 = mk_lid "lift1" in
                    register env1 uu____648 c_lift1 in
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
                      let uu____656 =
                        let uu____660 =
                          let uu____661 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____661 in
                        let uu____662 =
                          let uu____664 =
                            let uu____665 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____665 in
                          [uu____664] in
                        uu____660 :: uu____662 in
                      let uu____666 =
                        let uu____669 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____669 in
                      FStar_Syntax_Util.arrow uu____656 uu____666 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____672 =
                        let uu____673 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____673 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____672 in
                    let a2 =
                      let uu____675 =
                        let uu____676 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____676 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____675 in
                    let ret1 =
                      let uu____679 =
                        let uu____680 =
                          let uu____683 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____683 in
                        FStar_Syntax_Util.residual_tot uu____680 in
                      FStar_Pervasives_Native.Some uu____679 in
                    let uu____684 =
                      let uu____685 = mk_all_implicit binders in
                      let uu____689 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____685 uu____689 in
                    let uu____711 =
                      let uu____712 =
                        let uu____718 =
                          let uu____720 =
                            let uu____723 =
                              let uu____729 =
                                let uu____731 =
                                  let uu____734 =
                                    let uu____740 =
                                      let uu____742 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____742] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____740 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____734 in
                                let uu____743 =
                                  let uu____747 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____747] in
                                uu____731 :: uu____743 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____729 in
                            FStar_Syntax_Util.mk_app c_app1 uu____723 in
                          let uu____750 =
                            let uu____754 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____754] in
                          uu____720 :: uu____750 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____718 in
                      FStar_Syntax_Util.mk_app c_app1 uu____712 in
                    FStar_Syntax_Util.abs uu____684 uu____711 ret1 in
                  let c_lift21 =
                    let uu____758 = mk_lid "lift2" in
                    register env1 uu____758 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____765 =
                        let uu____769 =
                          let uu____770 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____770 in
                        [uu____769] in
                      let uu____771 =
                        let uu____774 =
                          let uu____775 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____775 in
                        FStar_Syntax_Syntax.mk_Total uu____774 in
                      FStar_Syntax_Util.arrow uu____765 uu____771 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____779 =
                        let uu____780 =
                          let uu____783 =
                            let uu____784 =
                              let uu____788 =
                                let uu____789 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____789 in
                              [uu____788] in
                            let uu____790 =
                              let uu____793 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____793 in
                            FStar_Syntax_Util.arrow uu____784 uu____790 in
                          mk_ctx uu____783 in
                        FStar_Syntax_Util.residual_tot uu____780 in
                      FStar_Pervasives_Native.Some uu____779 in
                    let e1 =
                      let uu____795 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____795 in
                    let body =
                      let uu____797 =
                        let uu____798 =
                          let uu____802 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____802] in
                        FStar_List.append gamma uu____798 in
                      let uu____805 =
                        let uu____806 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____809 =
                          let uu____815 =
                            let uu____816 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____816 in
                          let uu____817 = args_of_binders1 gamma in uu____815
                            :: uu____817 in
                        FStar_Syntax_Util.mk_app uu____806 uu____809 in
                      FStar_Syntax_Util.abs uu____797 uu____805 ret1 in
                    let uu____819 =
                      let uu____820 = mk_all_implicit binders in
                      let uu____824 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____820 uu____824 in
                    FStar_Syntax_Util.abs uu____819 body ret1 in
                  let c_push1 =
                    let uu____841 = mk_lid "push" in
                    register env1 uu____841 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____864 =
                        let uu____865 =
                          let uu____875 = args_of_binders1 binders in
                          (c, uu____875) in
                        FStar_Syntax_Syntax.Tm_app uu____865 in
                      mk1 uu____864
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____883 =
                        let uu____884 =
                          let uu____888 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____889 =
                            let uu____891 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____891] in
                          uu____888 :: uu____889 in
                        let uu____892 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____884 uu____892 in
                      FStar_Syntax_Syntax.mk_Total uu____883 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____896 =
                      let uu____897 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____897 in
                    let uu____903 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____905 =
                        let uu____908 =
                          let uu____914 =
                            let uu____916 =
                              let uu____919 =
                                let uu____925 =
                                  let uu____926 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____926 in
                                [uu____925] in
                              FStar_Syntax_Util.mk_app l_ite uu____919 in
                            [uu____916] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg uu____914 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____908 in
                      FStar_Syntax_Util.ascribe uu____905
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____896 uu____903
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____943 = mk_lid "wp_if_then_else" in
                    register env1 uu____943 wp_if_then_else in
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
                      let uu____954 =
                        let uu____960 =
                          let uu____962 =
                            let uu____965 =
                              let uu____971 =
                                let uu____973 =
                                  let uu____976 =
                                    let uu____982 =
                                      let uu____983 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____983 in
                                    [uu____982] in
                                  FStar_Syntax_Util.mk_app l_and uu____976 in
                                [uu____973] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____971 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____965 in
                          let uu____988 =
                            let uu____992 = FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____992] in
                          uu____962 :: uu____988 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____960 in
                      FStar_Syntax_Util.mk_app c_app1 uu____954 in
                    let uu____995 =
                      let uu____996 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____996 in
                    FStar_Syntax_Util.abs uu____995 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1003 = mk_lid "wp_assert" in
                    register env1 uu____1003 wp_assert in
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
                      let uu____1014 =
                        let uu____1020 =
                          let uu____1022 =
                            let uu____1025 =
                              let uu____1031 =
                                let uu____1033 =
                                  let uu____1036 =
                                    let uu____1042 =
                                      let uu____1043 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1043 in
                                    [uu____1042] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1036 in
                                [uu____1033] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1031 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1025 in
                          let uu____1048 =
                            let uu____1052 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1052] in
                          uu____1022 :: uu____1048 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1020 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1014 in
                    let uu____1055 =
                      let uu____1056 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1056 in
                    FStar_Syntax_Util.abs uu____1055 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1063 = mk_lid "wp_assume" in
                    register env1 uu____1063 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1072 =
                        let uu____1076 =
                          let uu____1077 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1077 in
                        [uu____1076] in
                      let uu____1078 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1072 uu____1078 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____1085 =
                        let uu____1091 =
                          let uu____1093 =
                            let uu____1096 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1096 in
                          let uu____1102 =
                            let uu____1106 =
                              let uu____1109 =
                                let uu____1115 =
                                  let uu____1117 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1117] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1115 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1109 in
                            [uu____1106] in
                          uu____1093 :: uu____1102 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1091 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1085 in
                    let uu____1124 =
                      let uu____1125 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1125 in
                    FStar_Syntax_Util.abs uu____1124 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1132 = mk_lid "wp_close" in
                    register env1 uu____1132 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1140 =
                      let uu____1141 =
                        let uu____1142 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1142 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1141 in
                    FStar_Pervasives_Native.Some uu____1140 in
                  let mk_forall1 x body =
                    let uu____1154 =
                      let uu____1157 =
                        let uu____1158 =
                          let uu____1168 =
                            let uu____1170 =
                              let uu____1171 =
                                let uu____1172 =
                                  let uu____1173 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1173] in
                                FStar_Syntax_Util.abs uu____1172 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1171 in
                            [uu____1170] in
                          (FStar_Syntax_Util.tforall, uu____1168) in
                        FStar_Syntax_Syntax.Tm_app uu____1158 in
                      FStar_Syntax_Syntax.mk uu____1157 in
                    uu____1154 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1187 =
                      let uu____1188 = FStar_Syntax_Subst.compress t in
                      uu____1188.FStar_Syntax_Syntax.n in
                    match uu____1187 with
                    | FStar_Syntax_Syntax.Tm_type uu____1191 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1209  ->
                              match uu____1209 with
                              | (b,uu____1213) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1214 -> true in
                  let rec is_monotonic t =
                    let uu____1219 =
                      let uu____1220 = FStar_Syntax_Subst.compress t in
                      uu____1220.FStar_Syntax_Syntax.n in
                    match uu____1219 with
                    | FStar_Syntax_Syntax.Tm_type uu____1223 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1241  ->
                              match uu____1241 with
                              | (b,uu____1245) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1246 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1298 =
                      let uu____1299 = FStar_Syntax_Subst.compress t1 in
                      uu____1299.FStar_Syntax_Syntax.n in
                    match uu____1298 with
                    | FStar_Syntax_Syntax.Tm_type uu____1302 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1305);
                                      FStar_Syntax_Syntax.tk = uu____1306;
                                      FStar_Syntax_Syntax.pos = uu____1307;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1329 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1329
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1332 =
                              let uu____1335 =
                                let uu____1341 =
                                  let uu____1342 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1342 in
                                [uu____1341] in
                              FStar_Syntax_Util.mk_app x uu____1335 in
                            let uu____1343 =
                              let uu____1346 =
                                let uu____1352 =
                                  let uu____1353 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1353 in
                                [uu____1352] in
                              FStar_Syntax_Util.mk_app y uu____1346 in
                            mk_rel1 b uu____1332 uu____1343 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1358 =
                               let uu____1359 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1362 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1359 uu____1362 in
                             let uu____1365 =
                               let uu____1366 =
                                 let uu____1369 =
                                   let uu____1375 =
                                     let uu____1376 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1376 in
                                   [uu____1375] in
                                 FStar_Syntax_Util.mk_app x uu____1369 in
                               let uu____1377 =
                                 let uu____1380 =
                                   let uu____1386 =
                                     let uu____1387 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1387 in
                                   [uu____1386] in
                                 FStar_Syntax_Util.mk_app y uu____1380 in
                               mk_rel1 b uu____1366 uu____1377 in
                             FStar_Syntax_Util.mk_imp uu____1358 uu____1365 in
                           let uu____1388 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1388)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1391);
                                      FStar_Syntax_Syntax.tk = uu____1392;
                                      FStar_Syntax_Syntax.pos = uu____1393;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1415 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1415
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1418 =
                              let uu____1421 =
                                let uu____1427 =
                                  let uu____1428 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1428 in
                                [uu____1427] in
                              FStar_Syntax_Util.mk_app x uu____1421 in
                            let uu____1429 =
                              let uu____1432 =
                                let uu____1438 =
                                  let uu____1439 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1439 in
                                [uu____1438] in
                              FStar_Syntax_Util.mk_app y uu____1432 in
                            mk_rel1 b uu____1418 uu____1429 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1444 =
                               let uu____1445 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1448 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1445 uu____1448 in
                             let uu____1451 =
                               let uu____1452 =
                                 let uu____1455 =
                                   let uu____1461 =
                                     let uu____1462 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1462 in
                                   [uu____1461] in
                                 FStar_Syntax_Util.mk_app x uu____1455 in
                               let uu____1463 =
                                 let uu____1466 =
                                   let uu____1472 =
                                     let uu____1473 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1473 in
                                   [uu____1472] in
                                 FStar_Syntax_Util.mk_app y uu____1466 in
                               mk_rel1 b uu____1452 uu____1463 in
                             FStar_Syntax_Util.mk_imp uu____1444 uu____1451 in
                           let uu____1474 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1474)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___103_1495 = t1 in
                          let uu____1496 =
                            let uu____1497 =
                              let uu____1505 =
                                let uu____1506 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1506 in
                              ([binder], uu____1505) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1497 in
                          {
                            FStar_Syntax_Syntax.n = uu____1496;
                            FStar_Syntax_Syntax.tk =
                              (uu___103_1495.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___103_1495.FStar_Syntax_Syntax.pos)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1516 ->
                        failwith "unhandled arrow"
                    | uu____1524 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1539 =
                        let uu____1540 = FStar_Syntax_Subst.compress t1 in
                        uu____1540.FStar_Syntax_Syntax.n in
                      match uu____1539 with
                      | FStar_Syntax_Syntax.Tm_type uu____1543 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1560 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1560
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1575 =
                                let uu____1576 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1576 i in
                              FStar_Syntax_Syntax.fvar uu____1575
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____1600 =
                            let uu____1604 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1615  ->
                                     match uu____1615 with
                                     | (t2,q) ->
                                         let uu____1620 = project i x in
                                         let uu____1621 = project i y in
                                         mk_stronger t2 uu____1620 uu____1621)
                                args in
                            match uu____1604 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1600 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1638);
                                      FStar_Syntax_Syntax.tk = uu____1639;
                                      FStar_Syntax_Syntax.pos = uu____1640;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1666  ->
                                   match uu____1666 with
                                   | (bv,q) ->
                                       let uu____1671 =
                                         let uu____1672 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1672 in
                                       FStar_Syntax_Syntax.gen_bv uu____1671
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1678 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1678) bvs in
                          let body =
                            let uu____1680 = FStar_Syntax_Util.mk_app x args in
                            let uu____1681 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1680 uu____1681 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1688);
                                      FStar_Syntax_Syntax.tk = uu____1689;
                                      FStar_Syntax_Syntax.pos = uu____1690;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1716  ->
                                   match uu____1716 with
                                   | (bv,q) ->
                                       let uu____1721 =
                                         let uu____1722 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1722 in
                                       FStar_Syntax_Syntax.gen_bv uu____1721
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1728 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1728) bvs in
                          let body =
                            let uu____1730 = FStar_Syntax_Util.mk_app x args in
                            let uu____1731 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1730 uu____1731 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1736 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1738 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1739 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1740 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1738 uu____1739 uu____1740 in
                    let uu____1741 =
                      let uu____1742 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1742 in
                    FStar_Syntax_Util.abs uu____1741 body ret_tot_type in
                  let stronger1 =
                    let uu____1757 = mk_lid "stronger" in
                    register env1 uu____1757 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1763 = FStar_Util.prefix gamma in
                    match uu____1763 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1789 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1789 in
                          let uu____1792 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1792 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____1800 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1800 in
                              let guard_free1 =
                                let uu____1807 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1807 in
                              let pat =
                                let uu____1811 =
                                  let uu____1817 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1817] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1811 in
                              let pattern_guarded_body =
                                let uu____1821 =
                                  let uu____1822 =
                                    let uu____1827 =
                                      let uu____1828 =
                                        let uu____1835 =
                                          let uu____1837 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1837] in
                                        [uu____1835] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1828 in
                                    (body, uu____1827) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1822 in
                                mk1 uu____1821 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1840 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1843 =
                            let uu____1844 =
                              let uu____1845 =
                                let uu____1846 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1849 =
                                  let uu____1855 = args_of_binders1 wp_args in
                                  let uu____1857 =
                                    let uu____1859 =
                                      let uu____1860 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1860 in
                                    [uu____1859] in
                                  FStar_List.append uu____1855 uu____1857 in
                                FStar_Syntax_Util.mk_app uu____1846
                                  uu____1849 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1845 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1844 in
                          FStar_Syntax_Util.abs gamma uu____1843
                            ret_gtot_type in
                        let uu____1861 =
                          let uu____1862 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1862 in
                        FStar_Syntax_Util.abs uu____1861 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1869 = mk_lid "wp_ite" in
                    register env1 uu____1869 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1875 = FStar_Util.prefix gamma in
                    match uu____1875 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1899 =
                            let uu____1900 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____1903 =
                              let uu____1909 =
                                let uu____1910 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1910 in
                              [uu____1909] in
                            FStar_Syntax_Util.mk_app uu____1900 uu____1903 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1899 in
                        let uu____1911 =
                          let uu____1912 =
                            let uu____1916 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1916 gamma in
                          FStar_List.append binders uu____1912 in
                        FStar_Syntax_Util.abs uu____1911 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1925 = mk_lid "null_wp" in
                    register env1 uu____1925 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____1934 =
                        let uu____1940 =
                          let uu____1942 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____1943 =
                            let uu____1945 =
                              let uu____1948 =
                                let uu____1954 =
                                  let uu____1955 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____1955 in
                                [uu____1954] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1948 in
                            let uu____1956 =
                              let uu____1960 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____1960] in
                            uu____1945 :: uu____1956 in
                          uu____1942 :: uu____1943 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1940 in
                      FStar_Syntax_Util.mk_app stronger2 uu____1934 in
                    let uu____1963 =
                      let uu____1964 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____1964 in
                    FStar_Syntax_Util.abs uu____1963 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____1971 = mk_lid "wp_trivial" in
                    register env1 uu____1971 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____1976 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____1976
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____1981 =
                      let uu____1983 = FStar_ST.read sigelts in
                      FStar_List.rev uu____1983 in
                    let uu____1988 =
                      let uu___104_1989 = ed in
                      let uu____1990 =
                        let uu____1991 = c wp_if_then_else2 in
                        ([], uu____1991) in
                      let uu____1993 =
                        let uu____1994 = c wp_ite2 in ([], uu____1994) in
                      let uu____1996 =
                        let uu____1997 = c stronger2 in ([], uu____1997) in
                      let uu____1999 =
                        let uu____2000 = c wp_close2 in ([], uu____2000) in
                      let uu____2002 =
                        let uu____2003 = c wp_assert2 in ([], uu____2003) in
                      let uu____2005 =
                        let uu____2006 = c wp_assume2 in ([], uu____2006) in
                      let uu____2008 =
                        let uu____2009 = c null_wp2 in ([], uu____2009) in
                      let uu____2011 =
                        let uu____2012 = c wp_trivial2 in ([], uu____2012) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___104_1989.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___104_1989.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___104_1989.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___104_1989.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___104_1989.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___104_1989.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___104_1989.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____1990;
                        FStar_Syntax_Syntax.ite_wp = uu____1993;
                        FStar_Syntax_Syntax.stronger = uu____1996;
                        FStar_Syntax_Syntax.close_wp = uu____1999;
                        FStar_Syntax_Syntax.assert_p = uu____2002;
                        FStar_Syntax_Syntax.assume_p = uu____2005;
                        FStar_Syntax_Syntax.null_wp = uu____2008;
                        FStar_Syntax_Syntax.trivial = uu____2011;
                        FStar_Syntax_Syntax.repr =
                          (uu___104_1989.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___104_1989.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___104_1989.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___104_1989.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____1981, uu____1988)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___105_2027 = dmff_env in
      {
        env = env';
        subst = (uu___105_2027.subst);
        tc_const = (uu___105_2027.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2041 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2055 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___91_2067  ->
    match uu___91_2067 with
    | FStar_Syntax_Syntax.Total (t,uu____2069) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___90_2079  ->
                match uu___90_2079 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2080 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2082 =
          let uu____2083 =
            let uu____2084 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2084 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2083 in
        failwith uu____2082
    | FStar_Syntax_Syntax.GTotal uu____2085 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___92_2094  ->
    match uu___92_2094 with
    | N t ->
        let uu____2096 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2096
    | M t ->
        let uu____2098 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2098
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2103,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2105;
                      FStar_Syntax_Syntax.pos = uu____2106;_})
        -> nm_of_comp n2
    | uu____2116 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2130 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2130 with | M uu____2131 -> true | N uu____2132 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2137 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2148 =
        let uu____2152 =
          let uu____2153 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2153 in
        [uu____2152] in
      let uu____2154 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2148 uu____2154 in
    let uu____2157 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2157
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
          (let uu____2194 =
             let uu____2202 =
               let uu____2206 =
                 let uu____2209 =
                   let uu____2210 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2210 in
                 let uu____2211 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2209, uu____2211) in
               [uu____2206] in
             let uu____2216 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2202, uu____2216) in
           FStar_Syntax_Syntax.Tm_arrow uu____2194)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2245) ->
          let binders1 =
            FStar_List.map
              (fun uu____2268  ->
                 match uu____2268 with
                 | (bv,aqual) ->
                     let uu____2275 =
                       let uu___106_2276 = bv in
                       let uu____2277 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_2276.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_2276.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2277
                       } in
                     (uu____2275, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2280,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2282);
                             FStar_Syntax_Syntax.tk = uu____2283;
                             FStar_Syntax_Syntax.pos = uu____2284;_})
               ->
               let uu____2300 =
                 let uu____2301 =
                   let uu____2309 =
                     let uu____2310 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2310 in
                   (binders1, uu____2309) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2301 in
               mk1 uu____2300
           | uu____2314 ->
               let uu____2315 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2315 with
                | N hn ->
                    let uu____2317 =
                      let uu____2318 =
                        let uu____2326 =
                          let uu____2327 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2327 in
                        (binders1, uu____2326) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2318 in
                    mk1 uu____2317
                | M a ->
                    let uu____2332 =
                      let uu____2333 =
                        let uu____2341 =
                          let uu____2345 =
                            let uu____2349 =
                              let uu____2352 =
                                let uu____2353 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2353 in
                              let uu____2354 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2352, uu____2354) in
                            [uu____2349] in
                          FStar_List.append binders1 uu____2345 in
                        let uu____2361 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2341, uu____2361) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2333 in
                    mk1 uu____2332))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2412 = f x in
                    FStar_Util.string_builder_append strb uu____2412);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2419 = f x1 in
                         FStar_Util.string_builder_append strb uu____2419))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2421 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2422 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2421 uu____2422 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2430 =
              let uu____2431 = FStar_Syntax_Subst.compress ty in
              uu____2431.FStar_Syntax_Syntax.n in
            match uu____2430 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2446 =
                  let uu____2447 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2447 in
                if uu____2446
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2470 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2470 s in
                       let uu____2472 =
                         let uu____2473 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2473 in
                       if uu____2472
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2476 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2476 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2492  ->
                                  match uu____2492 with
                                  | (bv,uu____2498) ->
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
            | uu____2514 ->
                ((let uu____2516 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2516);
                 false) in
          let rec is_valid_application head2 =
            let uu____2521 =
              let uu____2522 = FStar_Syntax_Subst.compress head2 in
              uu____2522.FStar_Syntax_Syntax.n in
            match uu____2521 with
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
                  (let uu____2527 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2527)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____2529 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____2529 with
                 | ((uu____2534,ty),uu____2536) ->
                     let uu____2539 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____2539
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____2549 -> true
                        | uu____2559 ->
                            ((let uu____2561 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____2561);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____2563 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2564 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2566) ->
                is_valid_application t2
            | uu____2571 -> false in
          let uu____2572 = is_valid_application head1 in
          if uu____2572
          then
            let uu____2573 =
              let uu____2574 =
                let uu____2584 =
                  FStar_List.map
                    (fun uu____2598  ->
                       match uu____2598 with
                       | (t2,qual) ->
                           let uu____2611 = star_type' env t2 in
                           (uu____2611, qual)) args in
                (head1, uu____2584) in
              FStar_Syntax_Syntax.Tm_app uu____2574 in
            mk1 uu____2573
          else
            (let uu____2618 =
               let uu____2619 =
                 let uu____2620 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2620 in
               FStar_Errors.Err uu____2619 in
             raise uu____2618)
      | FStar_Syntax_Syntax.Tm_bvar uu____2621 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2622 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2623 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2624 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2640 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2640 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___109_2646 = env in
                 let uu____2647 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2647;
                   subst = (uu___109_2646.subst);
                   tc_const = (uu___109_2646.tc_const)
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
               ((let uu___110_2665 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___110_2665.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___110_2665.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2672 =
            let uu____2673 =
              let uu____2678 = star_type' env t2 in (uu____2678, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2673 in
          mk1 uu____2672
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____2716 =
            let uu____2717 =
              let uu____2735 = star_type' env e in
              let uu____2736 =
                let uu____2746 =
                  let uu____2751 = star_type' env t2 in
                  FStar_Util.Inl uu____2751 in
                (uu____2746, FStar_Pervasives_Native.None) in
              (uu____2735, uu____2736, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2717 in
          mk1 uu____2716
      | FStar_Syntax_Syntax.Tm_ascribed uu____2773 ->
          let uu____2791 =
            let uu____2792 =
              let uu____2793 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2793 in
            FStar_Errors.Err uu____2792 in
          raise uu____2791
      | FStar_Syntax_Syntax.Tm_refine uu____2794 ->
          let uu____2799 =
            let uu____2800 =
              let uu____2801 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2801 in
            FStar_Errors.Err uu____2800 in
          raise uu____2799
      | FStar_Syntax_Syntax.Tm_uinst uu____2802 ->
          let uu____2807 =
            let uu____2808 =
              let uu____2809 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2809 in
            FStar_Errors.Err uu____2808 in
          raise uu____2807
      | FStar_Syntax_Syntax.Tm_constant uu____2810 ->
          let uu____2811 =
            let uu____2812 =
              let uu____2813 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2813 in
            FStar_Errors.Err uu____2812 in
          raise uu____2811
      | FStar_Syntax_Syntax.Tm_match uu____2814 ->
          let uu____2829 =
            let uu____2830 =
              let uu____2831 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2831 in
            FStar_Errors.Err uu____2830 in
          raise uu____2829
      | FStar_Syntax_Syntax.Tm_let uu____2832 ->
          let uu____2840 =
            let uu____2841 =
              let uu____2842 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2842 in
            FStar_Errors.Err uu____2841 in
          raise uu____2840
      | FStar_Syntax_Syntax.Tm_uvar uu____2843 ->
          let uu____2854 =
            let uu____2855 =
              let uu____2856 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2856 in
            FStar_Errors.Err uu____2855 in
          raise uu____2854
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2857 =
            let uu____2858 =
              let uu____2859 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2859 in
            FStar_Errors.Err uu____2858 in
          raise uu____2857
      | FStar_Syntax_Syntax.Tm_delayed uu____2860 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___94_2879  ->
    match uu___94_2879 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___93_2884  ->
                match uu___93_2884 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2885 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2890 =
      let uu____2891 = FStar_Syntax_Subst.compress t in
      uu____2891.FStar_Syntax_Syntax.n in
    match uu____2890 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2911 =
            let uu____2912 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____2912 in
          is_C uu____2911 in
        if r
        then
          ((let uu____2924 =
              let uu____2925 =
                FStar_List.for_all
                  (fun uu____2931  ->
                     match uu____2931 with | (h,uu____2935) -> is_C h) args in
              Prims.op_Negation uu____2925 in
            if uu____2924 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2939 =
              let uu____2940 =
                FStar_List.for_all
                  (fun uu____2947  ->
                     match uu____2947 with
                     | (h,uu____2951) ->
                         let uu____2952 = is_C h in
                         Prims.op_Negation uu____2952) args in
              Prims.op_Negation uu____2940 in
            if uu____2939 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2966 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____2966 with
         | M t1 ->
             ((let uu____2969 = is_C t1 in
               if uu____2969 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2973) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2979) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2985,uu____2986) -> is_C t1
    | uu____3015 -> false
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
          let uu____3045 =
            let uu____3046 =
              let uu____3056 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3057 =
                let uu____3061 =
                  let uu____3064 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3064) in
                [uu____3061] in
              (uu____3056, uu____3057) in
            FStar_Syntax_Syntax.Tm_app uu____3046 in
          mk1 uu____3045 in
        let uu____3072 =
          let uu____3073 = FStar_Syntax_Syntax.mk_binder p in [uu____3073] in
        FStar_Syntax_Util.abs uu____3072 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___95_3077  ->
    match uu___95_3077 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3078 -> false
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
        let return_if uu____3211 =
          match uu____3211 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3232 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3234 =
                       let uu____3235 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3235 in
                     Prims.op_Negation uu____3234) in
                if uu____3232
                then
                  let uu____3236 =
                    let uu____3237 =
                      let uu____3238 = FStar_Syntax_Print.term_to_string e in
                      let uu____3239 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3240 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3238 uu____3239 uu____3240 in
                    FStar_Errors.Err uu____3237 in
                  raise uu____3236
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3254 = mk_return env t1 s_e in
                     ((M t1), uu____3254, u_e)))
               | (M t1,N t2) ->
                   let uu____3257 =
                     let uu____3258 =
                       let uu____3259 = FStar_Syntax_Print.term_to_string e in
                       let uu____3260 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3261 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3259 uu____3260 uu____3261 in
                     FStar_Errors.Err uu____3258 in
                   raise uu____3257) in
        let ensure_m env1 e2 =
          let strip_m uu___96_3287 =
            match uu___96_3287 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3297 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3308 =
                let uu____3309 =
                  let uu____3312 =
                    let uu____3313 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3313 in
                  (uu____3312, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3309 in
              raise uu____3308
          | M uu____3317 ->
              let uu____3318 = check env1 e2 context_nm in strip_m uu____3318 in
        let uu____3322 =
          let uu____3323 = FStar_Syntax_Subst.compress e in
          uu____3323.FStar_Syntax_Syntax.n in
        match uu____3322 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3329 ->
            let uu____3330 = infer env e in return_if uu____3330
        | FStar_Syntax_Syntax.Tm_name uu____3334 ->
            let uu____3335 = infer env e in return_if uu____3335
        | FStar_Syntax_Syntax.Tm_fvar uu____3339 ->
            let uu____3340 = infer env e in return_if uu____3340
        | FStar_Syntax_Syntax.Tm_abs uu____3344 ->
            let uu____3354 = infer env e in return_if uu____3354
        | FStar_Syntax_Syntax.Tm_constant uu____3358 ->
            let uu____3359 = infer env e in return_if uu____3359
        | FStar_Syntax_Syntax.Tm_app uu____3363 ->
            let uu____3373 = infer env e in return_if uu____3373
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3422) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3428) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3434,uu____3435) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3464 ->
            let uu____3472 =
              let uu____3473 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3473 in
            failwith uu____3472
        | FStar_Syntax_Syntax.Tm_type uu____3477 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3481 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3492 ->
            let uu____3497 =
              let uu____3498 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3498 in
            failwith uu____3497
        | FStar_Syntax_Syntax.Tm_uvar uu____3502 ->
            let uu____3513 =
              let uu____3514 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3514 in
            failwith uu____3513
        | FStar_Syntax_Syntax.Tm_delayed uu____3518 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3536 =
              let uu____3537 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3537 in
            failwith uu____3536
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
      let uu____3559 =
        let uu____3560 = FStar_Syntax_Subst.compress e in
        uu____3560.FStar_Syntax_Syntax.n in
      match uu____3559 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____3599;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____3600;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____3605 =
                  let uu___111_3606 = rc in
                  let uu____3607 =
                    let uu____3611 =
                      let uu____3612 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____3612 in
                    FStar_Pervasives_Native.Some uu____3611 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___111_3606.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____3607;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___111_3606.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____3605 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___112_3621 = env in
            let uu____3622 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3622;
              subst = (uu___112_3621.subst);
              tc_const = (uu___112_3621.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3635  ->
                 match uu____3635 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_3644 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_3644.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_3644.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3645 =
            FStar_List.fold_left
              (fun uu____3666  ->
                 fun uu____3667  ->
                   match (uu____3666, uu____3667) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3695 = is_C c in
                       if uu____3695
                       then
                         let xw =
                           let uu____3700 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____3700 in
                         let x =
                           let uu___114_3702 = bv in
                           let uu____3703 =
                             let uu____3706 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3706 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_3702.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_3702.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3703
                           } in
                         let env3 =
                           let uu___115_3708 = env2 in
                           let uu____3709 =
                             let uu____3711 =
                               let uu____3712 =
                                 let uu____3717 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3717) in
                               FStar_Syntax_Syntax.NT uu____3712 in
                             uu____3711 :: (env2.subst) in
                           {
                             env = (uu___115_3708.env);
                             subst = uu____3709;
                             tc_const = (uu___115_3708.tc_const)
                           } in
                         let uu____3718 =
                           let uu____3720 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3721 =
                             let uu____3723 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3723 :: acc in
                           uu____3720 :: uu____3721 in
                         (env3, uu____3718)
                       else
                         (let x =
                            let uu___116_3727 = bv in
                            let uu____3728 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_3727.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_3727.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3728
                            } in
                          let uu____3731 =
                            let uu____3733 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3733 :: acc in
                          (env2, uu____3731))) (env1, []) binders1 in
          (match uu____3645 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3745 =
                 let check_what =
                   let uu____3757 = is_monadic rc_opt1 in
                   if uu____3757 then check_m else check_n in
                 let uu____3766 = check_what env2 body1 in
                 match uu____3766 with
                 | (t,s_body,u_body) ->
                     let uu____3776 =
                       let uu____3777 =
                         let uu____3778 = is_monadic rc_opt1 in
                         if uu____3778 then M t else N t in
                       comp_of_nm uu____3777 in
                     (uu____3776, s_body, u_body) in
               (match uu____3745 with
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
                                 let uu____3797 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___97_3800  ->
                                           match uu___97_3800 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____3801 -> false)) in
                                 if uu____3797
                                 then
                                   let uu____3802 =
                                     FStar_List.filter
                                       (fun uu___98_3805  ->
                                          match uu___98_3805 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____3806 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____3802
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____3815 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___99_3818  ->
                                         match uu___99_3818 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____3819 -> false)) in
                               if uu____3815
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___100_3824  ->
                                        match uu___100_3824 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____3825 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____3826 =
                                   let uu____3827 =
                                     let uu____3831 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____3831 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____3827 flags in
                                 FStar_Pervasives_Native.Some uu____3826
                               else
                                 (let uu____3833 =
                                    let uu___117_3834 = rc in
                                    let uu____3835 =
                                      let uu____3839 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____3839 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_3834.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____3835;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_3834.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____3833)) in
                    let uu____3840 =
                      let comp1 =
                        let uu____3847 = is_monadic rc_opt1 in
                        let uu____3848 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3847 uu____3848 in
                      let uu____3849 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____3849,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____3840 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____3882 =
                             let uu____3883 =
                               let uu____3893 =
                                 let uu____3895 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____3895 s_rc_opt in
                               (s_binders1, s_body1, uu____3893) in
                             FStar_Syntax_Syntax.Tm_abs uu____3883 in
                           mk1 uu____3882 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____3903 =
                             let uu____3904 =
                               let uu____3914 =
                                 let uu____3916 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____3916 u_rc_opt in
                               (u_binders2, u_body2, uu____3914) in
                             FStar_Syntax_Syntax.Tm_abs uu____3904 in
                           mk1 uu____3903 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____3924;_};
            FStar_Syntax_Syntax.fv_delta = uu____3925;
            FStar_Syntax_Syntax.fv_qual = uu____3926;_}
          ->
          let uu____3928 =
            let uu____3931 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3931 in
          (match uu____3928 with
           | (uu____3947,t) ->
               let uu____3949 = let uu____3950 = normalize1 t in N uu____3950 in
               (uu____3949, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3967 = check_n env head1 in
          (match uu____3967 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3981 =
                   let uu____3982 = FStar_Syntax_Subst.compress t in
                   uu____3982.FStar_Syntax_Syntax.n in
                 match uu____3981 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3985 -> true
                 | uu____3993 -> false in
               let rec flatten1 t =
                 let uu____4005 =
                   let uu____4006 = FStar_Syntax_Subst.compress t in
                   uu____4006.FStar_Syntax_Syntax.n in
                 match uu____4005 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4018);
                                FStar_Syntax_Syntax.tk = uu____4019;
                                FStar_Syntax_Syntax.pos = uu____4020;_})
                     when is_arrow t1 ->
                     let uu____4036 = flatten1 t1 in
                     (match uu____4036 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4088,uu____4089)
                     -> flatten1 e1
                 | uu____4118 ->
                     let uu____4119 =
                       let uu____4120 =
                         let uu____4121 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4121 in
                       FStar_Errors.Err uu____4120 in
                     raise uu____4119 in
               let uu____4129 = flatten1 t_head in
               (match uu____4129 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4181 =
                          let uu____4182 =
                            let uu____4183 = FStar_Util.string_of_int n1 in
                            let uu____4190 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4201 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4183 uu____4190 uu____4201 in
                          FStar_Errors.Err uu____4182 in
                        raise uu____4181)
                     else ();
                     (let uu____4209 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4209 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4236 args1 =
                            match uu____4236 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4279 =
                                       let uu____4280 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4280.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4279
                                 | (binders3,[]) ->
                                     let uu____4299 =
                                       let uu____4300 =
                                         let uu____4303 =
                                           let uu____4304 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4304 in
                                         FStar_Syntax_Subst.compress
                                           uu____4303 in
                                       uu____4300.FStar_Syntax_Syntax.n in
                                     (match uu____4299 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4320 =
                                            let uu____4321 =
                                              let uu____4322 =
                                                let uu____4330 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4330) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4322 in
                                            mk1 uu____4321 in
                                          N uu____4320
                                      | uu____4334 -> failwith "wat?")
                                 | ([],uu____4335::uu____4336) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4361)::binders3,(arg,uu____4364)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4398 = FStar_List.splitAt n' binders1 in
                          (match uu____4398 with
                           | (binders2,uu____4417) ->
                               let uu____4430 =
                                 let uu____4440 =
                                   FStar_List.map2
                                     (fun uu____4469  ->
                                        fun uu____4470  ->
                                          match (uu____4469, uu____4470) with
                                          | ((bv,uu____4487),(arg,q)) ->
                                              let uu____4494 =
                                                let uu____4495 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4495.FStar_Syntax_Syntax.n in
                                              (match uu____4494 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4505 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4518 ->
                                                   let uu____4519 =
                                                     check_n env arg in
                                                   (match uu____4519 with
                                                    | (uu____4530,s_arg,u_arg)
                                                        ->
                                                        let uu____4533 =
                                                          let uu____4537 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4537
                                                          then
                                                            let uu____4541 =
                                                              let uu____4544
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4544, q) in
                                                            [uu____4541;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4533))))
                                     binders2 args in
                                 FStar_List.split uu____4440 in
                               (match uu____4430 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4591 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4597 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4591, uu____4597)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4644) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4650) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4656,uu____4657) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4687 = let uu____4688 = env.tc_const c in N uu____4688 in
          (uu____4687, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4689 ->
          let uu____4697 =
            let uu____4698 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4698 in
          failwith uu____4697
      | FStar_Syntax_Syntax.Tm_type uu____4702 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4706 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4717 ->
          let uu____4722 =
            let uu____4723 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4723 in
          failwith uu____4722
      | FStar_Syntax_Syntax.Tm_uvar uu____4727 ->
          let uu____4738 =
            let uu____4739 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4739 in
          failwith uu____4738
      | FStar_Syntax_Syntax.Tm_delayed uu____4743 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4761 =
            let uu____4762 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4762 in
          failwith uu____4761
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
          let uu____4799 = check_n env e0 in
          match uu____4799 with
          | (uu____4806,s_e0,u_e0) ->
              let uu____4809 =
                let uu____4826 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4866 = FStar_Syntax_Subst.open_branch b in
                       match uu____4866 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___118_4895 = env in
                             let uu____4896 =
                               let uu____4897 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4897 in
                             {
                               env = uu____4896;
                               subst = (uu___118_4895.subst);
                               tc_const = (uu___118_4895.tc_const)
                             } in
                           let uu____4899 = f env1 body in
                           (match uu____4899 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____4945 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4826 in
              (match uu____4809 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5006 = FStar_List.hd nms in
                     match uu____5006 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___101_5012  ->
                          match uu___101_5012 with
                          | M uu____5013 -> true
                          | uu____5014 -> false) nms in
                   let uu____5015 =
                     let uu____5036 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5091  ->
                              match uu____5091 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5199 =
                                         check env original_body (M t2) in
                                       (match uu____5199 with
                                        | (uu____5220,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5245,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5036 in
                   (match uu____5015 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5358  ->
                                 match uu____5358 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5395 =
                                         let uu____5396 =
                                           let uu____5406 =
                                             let uu____5410 =
                                               let uu____5413 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5414 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5413, uu____5414) in
                                             [uu____5410] in
                                           (s_body, uu____5406) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5396 in
                                       mk1 uu____5395 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5435 =
                              let uu____5436 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5436] in
                            let uu____5437 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____5435 uu____5437
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____5442 =
                              let uu____5446 =
                                let uu____5447 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5447 in
                              [uu____5446] in
                            let uu____5448 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5442 uu____5448 in
                          let uu____5451 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____5481 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5451, uu____5481)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5495 =
                             let uu____5498 =
                               let uu____5499 =
                                 let uu____5517 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5517,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5499 in
                             mk1 uu____5498 in
                           let uu____5544 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5495, uu____5544))))
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
              let uu____5587 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5587] in
            let uu____5588 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5588 with
            | (x_binders1,e21) ->
                let uu____5596 = infer env e1 in
                (match uu____5596 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5607 = is_C t1 in
                       if uu____5607
                       then
                         let uu___119_5608 = binding in
                         let uu____5609 =
                           let uu____5612 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5612 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_5608.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_5608.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5609;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_5608.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_5608.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_5615 = env in
                       let uu____5616 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_5618 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_5618.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_5618.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5616;
                         subst = (uu___120_5615.subst);
                         tc_const = (uu___120_5615.tc_const)
                       } in
                     let uu____5619 = proceed env1 e21 in
                     (match uu____5619 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_5630 = binding in
                            let uu____5631 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_5630.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_5630.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5631;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_5630.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_5630.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5634 =
                            let uu____5637 =
                              let uu____5638 =
                                let uu____5646 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_5652 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_5652.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_5652.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_5652.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_5652.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5646) in
                              FStar_Syntax_Syntax.Tm_let uu____5638 in
                            mk1 uu____5637 in
                          let uu____5653 =
                            let uu____5656 =
                              let uu____5657 =
                                let uu____5665 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_5671 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_5671.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_5671.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_5671.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_5671.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5665) in
                              FStar_Syntax_Syntax.Tm_let uu____5657 in
                            mk1 uu____5656 in
                          (nm_rec, uu____5634, uu____5653))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_5680 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_5680.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_5680.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_5680.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_5682 = env in
                       let uu____5683 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_5685 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_5685.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_5685.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5683;
                         subst = (uu___126_5682.subst);
                         tc_const = (uu___126_5682.tc_const)
                       } in
                     let uu____5686 = ensure_m env1 e21 in
                     (match uu____5686 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____5703 =
                              let uu____5704 =
                                let uu____5714 =
                                  let uu____5718 =
                                    let uu____5721 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5722 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5721, uu____5722) in
                                  [uu____5718] in
                                (s_e2, uu____5714) in
                              FStar_Syntax_Syntax.Tm_app uu____5704 in
                            mk1 uu____5703 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____5734 =
                              let uu____5735 =
                                let uu____5745 =
                                  let uu____5749 =
                                    let uu____5752 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5752) in
                                  [uu____5749] in
                                (s_e1, uu____5745) in
                              FStar_Syntax_Syntax.Tm_app uu____5735 in
                            mk1 uu____5734 in
                          let uu____5760 =
                            let uu____5761 =
                              let uu____5762 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5762] in
                            FStar_Syntax_Util.abs uu____5761 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____5763 =
                            let uu____5766 =
                              let uu____5767 =
                                let uu____5775 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_5781 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_5781.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_5781.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_5781.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_5781.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5775) in
                              FStar_Syntax_Syntax.Tm_let uu____5767 in
                            mk1 uu____5766 in
                          ((M t2), uu____5760, uu____5763)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5790 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____5790 in
      let uu____5795 = check env e mn in
      match uu____5795 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5805 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5818 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____5818 in
      let uu____5823 = check env e mn in
      match uu____5823 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5833 -> failwith "[check_m]: impossible"
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
        (let uu____5855 =
           let uu____5856 = is_C c in Prims.op_Negation uu____5856 in
         if uu____5855 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____5868 =
           let uu____5869 = FStar_Syntax_Subst.compress c in
           uu____5869.FStar_Syntax_Syntax.n in
         match uu____5868 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5888 = FStar_Syntax_Util.head_and_args wp in
             (match uu____5888 with
              | (wp_head,wp_args) ->
                  ((let uu____5915 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5933 =
                           let uu____5934 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5934 in
                         Prims.op_Negation uu____5933) in
                    if uu____5915 then failwith "mismatch" else ());
                   (let uu____5946 =
                      let uu____5947 =
                        let uu____5957 =
                          FStar_List.map2
                            (fun uu____5976  ->
                               fun uu____5977  ->
                                 match (uu____5976, uu____5977) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6000 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6000
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6003 = print_implicit q in
                                         let uu____6004 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6003 uu____6004)
                                      else ();
                                      (let uu____6006 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6006, q)))) args wp_args in
                        (head1, uu____5957) in
                      FStar_Syntax_Syntax.Tm_app uu____5947 in
                    mk1 uu____5946)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6028 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6028 with
              | (binders_orig,comp1) ->
                  let uu____6033 =
                    let uu____6041 =
                      FStar_List.map
                        (fun uu____6062  ->
                           match uu____6062 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6075 = is_C h in
                               if uu____6075
                               then
                                 let w' =
                                   let uu____6082 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____6082 in
                                 let uu____6083 =
                                   let uu____6087 =
                                     let uu____6091 =
                                       let uu____6094 =
                                         let uu____6095 =
                                           let uu____6096 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6096 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6095 in
                                       (uu____6094, q) in
                                     [uu____6091] in
                                   (w', q) :: uu____6087 in
                                 (w', uu____6083)
                               else
                                 (let x =
                                    let uu____6108 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____6108 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6041 in
                  (match uu____6033 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6138 =
                           let uu____6140 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6140 in
                         FStar_Syntax_Subst.subst_comp uu____6138 comp1 in
                       let app =
                         let uu____6144 =
                           let uu____6145 =
                             let uu____6155 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6165 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6166 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6165, uu____6166)) bvs in
                             (wp, uu____6155) in
                           FStar_Syntax_Syntax.Tm_app uu____6145 in
                         mk1 uu____6144 in
                       let comp3 =
                         let uu____6171 = type_of_comp comp2 in
                         let uu____6172 = is_monadic_comp comp2 in
                         trans_G env uu____6171 uu____6172 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6174,uu____6175) ->
             trans_F_ env e wp
         | uu____6204 -> failwith "impossible trans_F_")
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
            let uu____6209 =
              let uu____6210 = star_type' env h in
              let uu____6213 =
                let uu____6219 =
                  let uu____6222 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6222) in
                [uu____6219] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6210;
                FStar_Syntax_Syntax.effect_args = uu____6213;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6209
          else
            (let uu____6228 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6228)
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
    fun t  -> let uu____6243 = n env.env t in star_type' env uu____6243
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____6257 = n env.env t in check_n env uu____6257
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6270 = n env.env c in
        let uu____6271 = n env.env wp in trans_F_ env uu____6270 uu____6271