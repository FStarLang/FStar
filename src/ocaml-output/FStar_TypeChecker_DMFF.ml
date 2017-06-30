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
                                      FStar_Syntax_Syntax.pos = uu____1307;
                                      FStar_Syntax_Syntax.vars = uu____1308;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1331 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1331
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1334 =
                              let uu____1337 =
                                let uu____1343 =
                                  let uu____1344 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1344 in
                                [uu____1343] in
                              FStar_Syntax_Util.mk_app x uu____1337 in
                            let uu____1345 =
                              let uu____1348 =
                                let uu____1354 =
                                  let uu____1355 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1355 in
                                [uu____1354] in
                              FStar_Syntax_Util.mk_app y uu____1348 in
                            mk_rel1 b uu____1334 uu____1345 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1360 =
                               let uu____1361 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1364 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1361 uu____1364 in
                             let uu____1367 =
                               let uu____1368 =
                                 let uu____1371 =
                                   let uu____1377 =
                                     let uu____1378 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1378 in
                                   [uu____1377] in
                                 FStar_Syntax_Util.mk_app x uu____1371 in
                               let uu____1379 =
                                 let uu____1382 =
                                   let uu____1388 =
                                     let uu____1389 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1389 in
                                   [uu____1388] in
                                 FStar_Syntax_Util.mk_app y uu____1382 in
                               mk_rel1 b uu____1368 uu____1379 in
                             FStar_Syntax_Util.mk_imp uu____1360 uu____1367 in
                           let uu____1390 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1390)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1393);
                                      FStar_Syntax_Syntax.tk = uu____1394;
                                      FStar_Syntax_Syntax.pos = uu____1395;
                                      FStar_Syntax_Syntax.vars = uu____1396;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1419 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1419
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1422 =
                              let uu____1425 =
                                let uu____1431 =
                                  let uu____1432 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1432 in
                                [uu____1431] in
                              FStar_Syntax_Util.mk_app x uu____1425 in
                            let uu____1433 =
                              let uu____1436 =
                                let uu____1442 =
                                  let uu____1443 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1443 in
                                [uu____1442] in
                              FStar_Syntax_Util.mk_app y uu____1436 in
                            mk_rel1 b uu____1422 uu____1433 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1448 =
                               let uu____1449 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1452 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1449 uu____1452 in
                             let uu____1455 =
                               let uu____1456 =
                                 let uu____1459 =
                                   let uu____1465 =
                                     let uu____1466 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1466 in
                                   [uu____1465] in
                                 FStar_Syntax_Util.mk_app x uu____1459 in
                               let uu____1467 =
                                 let uu____1470 =
                                   let uu____1476 =
                                     let uu____1477 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1477 in
                                   [uu____1476] in
                                 FStar_Syntax_Util.mk_app y uu____1470 in
                               mk_rel1 b uu____1456 uu____1467 in
                             FStar_Syntax_Util.mk_imp uu____1448 uu____1455 in
                           let uu____1478 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1478)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___103_1499 = t1 in
                          let uu____1500 =
                            let uu____1501 =
                              let uu____1509 =
                                let uu____1510 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1510 in
                              ([binder], uu____1509) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1501 in
                          {
                            FStar_Syntax_Syntax.n = uu____1500;
                            FStar_Syntax_Syntax.tk =
                              (uu___103_1499.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___103_1499.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___103_1499.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1522 ->
                        failwith "unhandled arrow"
                    | uu____1530 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1545 =
                        let uu____1546 = FStar_Syntax_Subst.compress t1 in
                        uu____1546.FStar_Syntax_Syntax.n in
                      match uu____1545 with
                      | FStar_Syntax_Syntax.Tm_type uu____1549 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1566 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1566
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1581 =
                                let uu____1582 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1582 i in
                              FStar_Syntax_Syntax.fvar uu____1581
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____1606 =
                            let uu____1610 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1621  ->
                                     match uu____1621 with
                                     | (t2,q) ->
                                         let uu____1626 = project i x in
                                         let uu____1627 = project i y in
                                         mk_stronger t2 uu____1626 uu____1627)
                                args in
                            match uu____1610 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1606 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1644);
                                      FStar_Syntax_Syntax.tk = uu____1645;
                                      FStar_Syntax_Syntax.pos = uu____1646;
                                      FStar_Syntax_Syntax.vars = uu____1647;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1674  ->
                                   match uu____1674 with
                                   | (bv,q) ->
                                       let uu____1679 =
                                         let uu____1680 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1680 in
                                       FStar_Syntax_Syntax.gen_bv uu____1679
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1686 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1686) bvs in
                          let body =
                            let uu____1688 = FStar_Syntax_Util.mk_app x args in
                            let uu____1689 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1688 uu____1689 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1696);
                                      FStar_Syntax_Syntax.tk = uu____1697;
                                      FStar_Syntax_Syntax.pos = uu____1698;
                                      FStar_Syntax_Syntax.vars = uu____1699;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1726  ->
                                   match uu____1726 with
                                   | (bv,q) ->
                                       let uu____1731 =
                                         let uu____1732 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1732 in
                                       FStar_Syntax_Syntax.gen_bv uu____1731
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1738 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1738) bvs in
                          let body =
                            let uu____1740 = FStar_Syntax_Util.mk_app x args in
                            let uu____1741 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1740 uu____1741 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1746 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1748 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1749 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1750 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1748 uu____1749 uu____1750 in
                    let uu____1751 =
                      let uu____1752 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1752 in
                    FStar_Syntax_Util.abs uu____1751 body ret_tot_type in
                  let stronger1 =
                    let uu____1767 = mk_lid "stronger" in
                    register env1 uu____1767 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1773 = FStar_Util.prefix gamma in
                    match uu____1773 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1799 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1799 in
                          let uu____1802 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1802 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____1810 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1810 in
                              let guard_free1 =
                                let uu____1817 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1817 in
                              let pat =
                                let uu____1821 =
                                  let uu____1827 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1827] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1821 in
                              let pattern_guarded_body =
                                let uu____1831 =
                                  let uu____1832 =
                                    let uu____1837 =
                                      let uu____1838 =
                                        let uu____1845 =
                                          let uu____1847 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1847] in
                                        [uu____1845] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1838 in
                                    (body, uu____1837) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1832 in
                                mk1 uu____1831 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1850 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1853 =
                            let uu____1854 =
                              let uu____1855 =
                                let uu____1856 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1859 =
                                  let uu____1865 = args_of_binders1 wp_args in
                                  let uu____1867 =
                                    let uu____1869 =
                                      let uu____1870 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1870 in
                                    [uu____1869] in
                                  FStar_List.append uu____1865 uu____1867 in
                                FStar_Syntax_Util.mk_app uu____1856
                                  uu____1859 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1855 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1854 in
                          FStar_Syntax_Util.abs gamma uu____1853
                            ret_gtot_type in
                        let uu____1871 =
                          let uu____1872 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1872 in
                        FStar_Syntax_Util.abs uu____1871 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1879 = mk_lid "wp_ite" in
                    register env1 uu____1879 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1885 = FStar_Util.prefix gamma in
                    match uu____1885 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1909 =
                            let uu____1910 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____1913 =
                              let uu____1919 =
                                let uu____1920 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1920 in
                              [uu____1919] in
                            FStar_Syntax_Util.mk_app uu____1910 uu____1913 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1909 in
                        let uu____1921 =
                          let uu____1922 =
                            let uu____1926 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1926 gamma in
                          FStar_List.append binders uu____1922 in
                        FStar_Syntax_Util.abs uu____1921 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1935 = mk_lid "null_wp" in
                    register env1 uu____1935 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____1944 =
                        let uu____1950 =
                          let uu____1952 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____1953 =
                            let uu____1955 =
                              let uu____1958 =
                                let uu____1964 =
                                  let uu____1965 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____1965 in
                                [uu____1964] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1958 in
                            let uu____1966 =
                              let uu____1970 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____1970] in
                            uu____1955 :: uu____1966 in
                          uu____1952 :: uu____1953 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1950 in
                      FStar_Syntax_Util.mk_app stronger2 uu____1944 in
                    let uu____1973 =
                      let uu____1974 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____1974 in
                    FStar_Syntax_Util.abs uu____1973 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____1981 = mk_lid "wp_trivial" in
                    register env1 uu____1981 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____1986 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____1986
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____1991 =
                      let uu____1993 = FStar_ST.read sigelts in
                      FStar_List.rev uu____1993 in
                    let uu____1998 =
                      let uu___104_1999 = ed in
                      let uu____2000 =
                        let uu____2001 = c wp_if_then_else2 in
                        ([], uu____2001) in
                      let uu____2003 =
                        let uu____2004 = c wp_ite2 in ([], uu____2004) in
                      let uu____2006 =
                        let uu____2007 = c stronger2 in ([], uu____2007) in
                      let uu____2009 =
                        let uu____2010 = c wp_close2 in ([], uu____2010) in
                      let uu____2012 =
                        let uu____2013 = c wp_assert2 in ([], uu____2013) in
                      let uu____2015 =
                        let uu____2016 = c wp_assume2 in ([], uu____2016) in
                      let uu____2018 =
                        let uu____2019 = c null_wp2 in ([], uu____2019) in
                      let uu____2021 =
                        let uu____2022 = c wp_trivial2 in ([], uu____2022) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___104_1999.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___104_1999.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___104_1999.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___104_1999.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___104_1999.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___104_1999.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___104_1999.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2000;
                        FStar_Syntax_Syntax.ite_wp = uu____2003;
                        FStar_Syntax_Syntax.stronger = uu____2006;
                        FStar_Syntax_Syntax.close_wp = uu____2009;
                        FStar_Syntax_Syntax.assert_p = uu____2012;
                        FStar_Syntax_Syntax.assume_p = uu____2015;
                        FStar_Syntax_Syntax.null_wp = uu____2018;
                        FStar_Syntax_Syntax.trivial = uu____2021;
                        FStar_Syntax_Syntax.repr =
                          (uu___104_1999.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___104_1999.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___104_1999.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___104_1999.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____1991, uu____1998)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___105_2037 = dmff_env in
      {
        env = env';
        subst = (uu___105_2037.subst);
        tc_const = (uu___105_2037.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2051 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2065 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___91_2077  ->
    match uu___91_2077 with
    | FStar_Syntax_Syntax.Total (t,uu____2079) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___90_2089  ->
                match uu___90_2089 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2090 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2092 =
          let uu____2093 =
            let uu____2094 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2094 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2093 in
        failwith uu____2092
    | FStar_Syntax_Syntax.GTotal uu____2095 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___92_2104  ->
    match uu___92_2104 with
    | N t ->
        let uu____2106 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2106
    | M t ->
        let uu____2108 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2108
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2113,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2115;
                      FStar_Syntax_Syntax.pos = uu____2116;
                      FStar_Syntax_Syntax.vars = uu____2117;_})
        -> nm_of_comp n2
    | uu____2128 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2142 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2142 with | M uu____2143 -> true | N uu____2144 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2149 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2160 =
        let uu____2164 =
          let uu____2165 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2165 in
        [uu____2164] in
      let uu____2166 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2160 uu____2166 in
    let uu____2169 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2169
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
          (let uu____2206 =
             let uu____2214 =
               let uu____2218 =
                 let uu____2221 =
                   let uu____2222 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2222 in
                 let uu____2223 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2221, uu____2223) in
               [uu____2218] in
             let uu____2228 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2214, uu____2228) in
           FStar_Syntax_Syntax.Tm_arrow uu____2206)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2257) ->
          let binders1 =
            FStar_List.map
              (fun uu____2280  ->
                 match uu____2280 with
                 | (bv,aqual) ->
                     let uu____2287 =
                       let uu___106_2288 = bv in
                       let uu____2289 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_2288.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_2288.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2289
                       } in
                     (uu____2287, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2292,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2294);
                             FStar_Syntax_Syntax.tk = uu____2295;
                             FStar_Syntax_Syntax.pos = uu____2296;
                             FStar_Syntax_Syntax.vars = uu____2297;_})
               ->
               let uu____2314 =
                 let uu____2315 =
                   let uu____2323 =
                     let uu____2324 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2324 in
                   (binders1, uu____2323) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2315 in
               mk1 uu____2314
           | uu____2328 ->
               let uu____2329 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2329 with
                | N hn ->
                    let uu____2331 =
                      let uu____2332 =
                        let uu____2340 =
                          let uu____2341 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2341 in
                        (binders1, uu____2340) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2332 in
                    mk1 uu____2331
                | M a ->
                    let uu____2346 =
                      let uu____2347 =
                        let uu____2355 =
                          let uu____2359 =
                            let uu____2363 =
                              let uu____2366 =
                                let uu____2367 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2367 in
                              let uu____2368 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2366, uu____2368) in
                            [uu____2363] in
                          FStar_List.append binders1 uu____2359 in
                        let uu____2375 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2355, uu____2375) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2347 in
                    mk1 uu____2346))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2426 = f x in
                    FStar_Util.string_builder_append strb uu____2426);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2433 = f x1 in
                         FStar_Util.string_builder_append strb uu____2433))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2435 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2436 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2435 uu____2436 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2444 =
              let uu____2445 = FStar_Syntax_Subst.compress ty in
              uu____2445.FStar_Syntax_Syntax.n in
            match uu____2444 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2460 =
                  let uu____2461 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2461 in
                if uu____2460
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2484 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2484 s in
                       let uu____2486 =
                         let uu____2487 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2487 in
                       if uu____2486
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2490 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2490 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2506  ->
                                  match uu____2506 with
                                  | (bv,uu____2512) ->
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
            | uu____2528 ->
                ((let uu____2530 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2530);
                 false) in
          let rec is_valid_application head2 =
            let uu____2535 =
              let uu____2536 = FStar_Syntax_Subst.compress head2 in
              uu____2536.FStar_Syntax_Syntax.n in
            match uu____2535 with
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
                  (let uu____2541 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2541)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____2543 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____2543 with
                 | ((uu____2548,ty),uu____2550) ->
                     let uu____2553 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____2553
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____2563 -> true
                        | uu____2573 ->
                            ((let uu____2575 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____2575);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____2577 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2578 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2580) ->
                is_valid_application t2
            | uu____2585 -> false in
          let uu____2586 = is_valid_application head1 in
          if uu____2586
          then
            let uu____2587 =
              let uu____2588 =
                let uu____2598 =
                  FStar_List.map
                    (fun uu____2612  ->
                       match uu____2612 with
                       | (t2,qual) ->
                           let uu____2625 = star_type' env t2 in
                           (uu____2625, qual)) args in
                (head1, uu____2598) in
              FStar_Syntax_Syntax.Tm_app uu____2588 in
            mk1 uu____2587
          else
            (let uu____2632 =
               let uu____2633 =
                 let uu____2634 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2634 in
               FStar_Errors.Err uu____2633 in
             raise uu____2632)
      | FStar_Syntax_Syntax.Tm_bvar uu____2635 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2636 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2637 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2638 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2654 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2654 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___109_2660 = env in
                 let uu____2661 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2661;
                   subst = (uu___109_2660.subst);
                   tc_const = (uu___109_2660.tc_const)
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
               ((let uu___110_2679 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___110_2679.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___110_2679.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2686 =
            let uu____2687 =
              let uu____2692 = star_type' env t2 in (uu____2692, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2687 in
          mk1 uu____2686
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____2730 =
            let uu____2731 =
              let uu____2749 = star_type' env e in
              let uu____2750 =
                let uu____2760 =
                  let uu____2765 = star_type' env t2 in
                  FStar_Util.Inl uu____2765 in
                (uu____2760, FStar_Pervasives_Native.None) in
              (uu____2749, uu____2750, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2731 in
          mk1 uu____2730
      | FStar_Syntax_Syntax.Tm_ascribed uu____2787 ->
          let uu____2805 =
            let uu____2806 =
              let uu____2807 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2807 in
            FStar_Errors.Err uu____2806 in
          raise uu____2805
      | FStar_Syntax_Syntax.Tm_refine uu____2808 ->
          let uu____2813 =
            let uu____2814 =
              let uu____2815 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2815 in
            FStar_Errors.Err uu____2814 in
          raise uu____2813
      | FStar_Syntax_Syntax.Tm_uinst uu____2816 ->
          let uu____2821 =
            let uu____2822 =
              let uu____2823 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2823 in
            FStar_Errors.Err uu____2822 in
          raise uu____2821
      | FStar_Syntax_Syntax.Tm_constant uu____2824 ->
          let uu____2825 =
            let uu____2826 =
              let uu____2827 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2827 in
            FStar_Errors.Err uu____2826 in
          raise uu____2825
      | FStar_Syntax_Syntax.Tm_match uu____2828 ->
          let uu____2843 =
            let uu____2844 =
              let uu____2845 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2845 in
            FStar_Errors.Err uu____2844 in
          raise uu____2843
      | FStar_Syntax_Syntax.Tm_let uu____2846 ->
          let uu____2854 =
            let uu____2855 =
              let uu____2856 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2856 in
            FStar_Errors.Err uu____2855 in
          raise uu____2854
      | FStar_Syntax_Syntax.Tm_uvar uu____2857 ->
          let uu____2868 =
            let uu____2869 =
              let uu____2870 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2870 in
            FStar_Errors.Err uu____2869 in
          raise uu____2868
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2871 =
            let uu____2872 =
              let uu____2873 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2873 in
            FStar_Errors.Err uu____2872 in
          raise uu____2871
      | FStar_Syntax_Syntax.Tm_delayed uu____2874 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___94_2893  ->
    match uu___94_2893 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___93_2898  ->
                match uu___93_2898 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2899 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2904 =
      let uu____2905 = FStar_Syntax_Subst.compress t in
      uu____2905.FStar_Syntax_Syntax.n in
    match uu____2904 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2925 =
            let uu____2926 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____2926 in
          is_C uu____2925 in
        if r
        then
          ((let uu____2938 =
              let uu____2939 =
                FStar_List.for_all
                  (fun uu____2945  ->
                     match uu____2945 with | (h,uu____2949) -> is_C h) args in
              Prims.op_Negation uu____2939 in
            if uu____2938 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2953 =
              let uu____2954 =
                FStar_List.for_all
                  (fun uu____2961  ->
                     match uu____2961 with
                     | (h,uu____2965) ->
                         let uu____2966 = is_C h in
                         Prims.op_Negation uu____2966) args in
              Prims.op_Negation uu____2954 in
            if uu____2953 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2980 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____2980 with
         | M t1 ->
             ((let uu____2983 = is_C t1 in
               if uu____2983 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2987) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2993) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2999,uu____3000) -> is_C t1
    | uu____3029 -> false
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
          let uu____3059 =
            let uu____3060 =
              let uu____3070 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3071 =
                let uu____3075 =
                  let uu____3078 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3078) in
                [uu____3075] in
              (uu____3070, uu____3071) in
            FStar_Syntax_Syntax.Tm_app uu____3060 in
          mk1 uu____3059 in
        let uu____3086 =
          let uu____3087 = FStar_Syntax_Syntax.mk_binder p in [uu____3087] in
        FStar_Syntax_Util.abs uu____3086 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___95_3091  ->
    match uu___95_3091 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3092 -> false
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
        let return_if uu____3225 =
          match uu____3225 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3246 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3248 =
                       let uu____3249 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3249 in
                     Prims.op_Negation uu____3248) in
                if uu____3246
                then
                  let uu____3250 =
                    let uu____3251 =
                      let uu____3252 = FStar_Syntax_Print.term_to_string e in
                      let uu____3253 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3254 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3252 uu____3253 uu____3254 in
                    FStar_Errors.Err uu____3251 in
                  raise uu____3250
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3268 = mk_return env t1 s_e in
                     ((M t1), uu____3268, u_e)))
               | (M t1,N t2) ->
                   let uu____3271 =
                     let uu____3272 =
                       let uu____3273 = FStar_Syntax_Print.term_to_string e in
                       let uu____3274 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3275 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3273 uu____3274 uu____3275 in
                     FStar_Errors.Err uu____3272 in
                   raise uu____3271) in
        let ensure_m env1 e2 =
          let strip_m uu___96_3301 =
            match uu___96_3301 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3311 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3322 =
                let uu____3323 =
                  let uu____3326 =
                    let uu____3327 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3327 in
                  (uu____3326, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3323 in
              raise uu____3322
          | M uu____3331 ->
              let uu____3332 = check env1 e2 context_nm in strip_m uu____3332 in
        let uu____3336 =
          let uu____3337 = FStar_Syntax_Subst.compress e in
          uu____3337.FStar_Syntax_Syntax.n in
        match uu____3336 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3343 ->
            let uu____3344 = infer env e in return_if uu____3344
        | FStar_Syntax_Syntax.Tm_name uu____3348 ->
            let uu____3349 = infer env e in return_if uu____3349
        | FStar_Syntax_Syntax.Tm_fvar uu____3353 ->
            let uu____3354 = infer env e in return_if uu____3354
        | FStar_Syntax_Syntax.Tm_abs uu____3358 ->
            let uu____3368 = infer env e in return_if uu____3368
        | FStar_Syntax_Syntax.Tm_constant uu____3372 ->
            let uu____3373 = infer env e in return_if uu____3373
        | FStar_Syntax_Syntax.Tm_app uu____3377 ->
            let uu____3387 = infer env e in return_if uu____3387
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3436) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3442) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3448,uu____3449) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3478 ->
            let uu____3486 =
              let uu____3487 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3487 in
            failwith uu____3486
        | FStar_Syntax_Syntax.Tm_type uu____3491 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3495 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3506 ->
            let uu____3511 =
              let uu____3512 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3512 in
            failwith uu____3511
        | FStar_Syntax_Syntax.Tm_uvar uu____3516 ->
            let uu____3527 =
              let uu____3528 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3528 in
            failwith uu____3527
        | FStar_Syntax_Syntax.Tm_delayed uu____3532 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3550 =
              let uu____3551 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3551 in
            failwith uu____3550
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
      let uu____3573 =
        let uu____3574 = FStar_Syntax_Subst.compress e in
        uu____3574.FStar_Syntax_Syntax.n in
      match uu____3573 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____3613;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____3614;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____3619 =
                  let uu___111_3620 = rc in
                  let uu____3621 =
                    let uu____3625 =
                      let uu____3626 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____3626 in
                    FStar_Pervasives_Native.Some uu____3625 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___111_3620.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____3621;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___111_3620.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____3619 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___112_3635 = env in
            let uu____3636 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3636;
              subst = (uu___112_3635.subst);
              tc_const = (uu___112_3635.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3649  ->
                 match uu____3649 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_3658 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_3658.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_3658.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3659 =
            FStar_List.fold_left
              (fun uu____3680  ->
                 fun uu____3681  ->
                   match (uu____3680, uu____3681) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3709 = is_C c in
                       if uu____3709
                       then
                         let xw =
                           let uu____3714 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____3714 in
                         let x =
                           let uu___114_3716 = bv in
                           let uu____3717 =
                             let uu____3720 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3720 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_3716.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_3716.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3717
                           } in
                         let env3 =
                           let uu___115_3722 = env2 in
                           let uu____3723 =
                             let uu____3725 =
                               let uu____3726 =
                                 let uu____3731 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3731) in
                               FStar_Syntax_Syntax.NT uu____3726 in
                             uu____3725 :: (env2.subst) in
                           {
                             env = (uu___115_3722.env);
                             subst = uu____3723;
                             tc_const = (uu___115_3722.tc_const)
                           } in
                         let uu____3732 =
                           let uu____3734 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3735 =
                             let uu____3737 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3737 :: acc in
                           uu____3734 :: uu____3735 in
                         (env3, uu____3732)
                       else
                         (let x =
                            let uu___116_3741 = bv in
                            let uu____3742 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_3741.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_3741.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3742
                            } in
                          let uu____3745 =
                            let uu____3747 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3747 :: acc in
                          (env2, uu____3745))) (env1, []) binders1 in
          (match uu____3659 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3759 =
                 let check_what =
                   let uu____3771 = is_monadic rc_opt1 in
                   if uu____3771 then check_m else check_n in
                 let uu____3780 = check_what env2 body1 in
                 match uu____3780 with
                 | (t,s_body,u_body) ->
                     let uu____3790 =
                       let uu____3791 =
                         let uu____3792 = is_monadic rc_opt1 in
                         if uu____3792 then M t else N t in
                       comp_of_nm uu____3791 in
                     (uu____3790, s_body, u_body) in
               (match uu____3759 with
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
                                 let uu____3811 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___97_3814  ->
                                           match uu___97_3814 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____3815 -> false)) in
                                 if uu____3811
                                 then
                                   let uu____3816 =
                                     FStar_List.filter
                                       (fun uu___98_3819  ->
                                          match uu___98_3819 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____3820 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____3816
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____3829 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___99_3832  ->
                                         match uu___99_3832 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____3833 -> false)) in
                               if uu____3829
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___100_3838  ->
                                        match uu___100_3838 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____3839 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____3840 =
                                   let uu____3841 =
                                     let uu____3845 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____3845 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____3841 flags in
                                 FStar_Pervasives_Native.Some uu____3840
                               else
                                 (let uu____3847 =
                                    let uu___117_3848 = rc in
                                    let uu____3849 =
                                      let uu____3853 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____3853 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_3848.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____3849;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_3848.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____3847)) in
                    let uu____3854 =
                      let comp1 =
                        let uu____3861 = is_monadic rc_opt1 in
                        let uu____3862 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3861 uu____3862 in
                      let uu____3863 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____3863,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____3854 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____3896 =
                             let uu____3897 =
                               let uu____3907 =
                                 let uu____3909 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____3909 s_rc_opt in
                               (s_binders1, s_body1, uu____3907) in
                             FStar_Syntax_Syntax.Tm_abs uu____3897 in
                           mk1 uu____3896 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____3917 =
                             let uu____3918 =
                               let uu____3928 =
                                 let uu____3930 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____3930 u_rc_opt in
                               (u_binders2, u_body2, uu____3928) in
                             FStar_Syntax_Syntax.Tm_abs uu____3918 in
                           mk1 uu____3917 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____3938;_};
            FStar_Syntax_Syntax.fv_delta = uu____3939;
            FStar_Syntax_Syntax.fv_qual = uu____3940;_}
          ->
          let uu____3942 =
            let uu____3945 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3945 in
          (match uu____3942 with
           | (uu____3961,t) ->
               let uu____3963 = let uu____3964 = normalize1 t in N uu____3964 in
               (uu____3963, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3981 = check_n env head1 in
          (match uu____3981 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3995 =
                   let uu____3996 = FStar_Syntax_Subst.compress t in
                   uu____3996.FStar_Syntax_Syntax.n in
                 match uu____3995 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3999 -> true
                 | uu____4007 -> false in
               let rec flatten1 t =
                 let uu____4019 =
                   let uu____4020 = FStar_Syntax_Subst.compress t in
                   uu____4020.FStar_Syntax_Syntax.n in
                 match uu____4019 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4032);
                                FStar_Syntax_Syntax.tk = uu____4033;
                                FStar_Syntax_Syntax.pos = uu____4034;
                                FStar_Syntax_Syntax.vars = uu____4035;_})
                     when is_arrow t1 ->
                     let uu____4052 = flatten1 t1 in
                     (match uu____4052 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4104,uu____4105)
                     -> flatten1 e1
                 | uu____4134 ->
                     let uu____4135 =
                       let uu____4136 =
                         let uu____4137 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4137 in
                       FStar_Errors.Err uu____4136 in
                     raise uu____4135 in
               let uu____4145 = flatten1 t_head in
               (match uu____4145 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4197 =
                          let uu____4198 =
                            let uu____4199 = FStar_Util.string_of_int n1 in
                            let uu____4206 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4217 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4199 uu____4206 uu____4217 in
                          FStar_Errors.Err uu____4198 in
                        raise uu____4197)
                     else ();
                     (let uu____4225 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4225 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4252 args1 =
                            match uu____4252 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4295 =
                                       let uu____4296 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4296.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4295
                                 | (binders3,[]) ->
                                     let uu____4315 =
                                       let uu____4316 =
                                         let uu____4319 =
                                           let uu____4320 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4320 in
                                         FStar_Syntax_Subst.compress
                                           uu____4319 in
                                       uu____4316.FStar_Syntax_Syntax.n in
                                     (match uu____4315 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4336 =
                                            let uu____4337 =
                                              let uu____4338 =
                                                let uu____4346 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4346) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4338 in
                                            mk1 uu____4337 in
                                          N uu____4336
                                      | uu____4350 -> failwith "wat?")
                                 | ([],uu____4351::uu____4352) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4377)::binders3,(arg,uu____4380)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4414 = FStar_List.splitAt n' binders1 in
                          (match uu____4414 with
                           | (binders2,uu____4433) ->
                               let uu____4446 =
                                 let uu____4456 =
                                   FStar_List.map2
                                     (fun uu____4485  ->
                                        fun uu____4486  ->
                                          match (uu____4485, uu____4486) with
                                          | ((bv,uu____4503),(arg,q)) ->
                                              let uu____4510 =
                                                let uu____4511 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4511.FStar_Syntax_Syntax.n in
                                              (match uu____4510 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4521 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4534 ->
                                                   let uu____4535 =
                                                     check_n env arg in
                                                   (match uu____4535 with
                                                    | (uu____4546,s_arg,u_arg)
                                                        ->
                                                        let uu____4549 =
                                                          let uu____4553 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4553
                                                          then
                                                            let uu____4557 =
                                                              let uu____4560
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4560, q) in
                                                            [uu____4557;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4549))))
                                     binders2 args in
                                 FStar_List.split uu____4456 in
                               (match uu____4446 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4607 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4613 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4607, uu____4613)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4660) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4666) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4672,uu____4673) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4703 = let uu____4704 = env.tc_const c in N uu____4704 in
          (uu____4703, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4705 ->
          let uu____4713 =
            let uu____4714 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4714 in
          failwith uu____4713
      | FStar_Syntax_Syntax.Tm_type uu____4718 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4722 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4733 ->
          let uu____4738 =
            let uu____4739 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4739 in
          failwith uu____4738
      | FStar_Syntax_Syntax.Tm_uvar uu____4743 ->
          let uu____4754 =
            let uu____4755 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4755 in
          failwith uu____4754
      | FStar_Syntax_Syntax.Tm_delayed uu____4759 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4777 =
            let uu____4778 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4778 in
          failwith uu____4777
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
          let uu____4815 = check_n env e0 in
          match uu____4815 with
          | (uu____4822,s_e0,u_e0) ->
              let uu____4825 =
                let uu____4842 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4882 = FStar_Syntax_Subst.open_branch b in
                       match uu____4882 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___118_4911 = env in
                             let uu____4912 =
                               let uu____4913 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4913 in
                             {
                               env = uu____4912;
                               subst = (uu___118_4911.subst);
                               tc_const = (uu___118_4911.tc_const)
                             } in
                           let uu____4915 = f env1 body in
                           (match uu____4915 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____4961 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4842 in
              (match uu____4825 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5022 = FStar_List.hd nms in
                     match uu____5022 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___101_5028  ->
                          match uu___101_5028 with
                          | M uu____5029 -> true
                          | uu____5030 -> false) nms in
                   let uu____5031 =
                     let uu____5052 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5107  ->
                              match uu____5107 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5215 =
                                         check env original_body (M t2) in
                                       (match uu____5215 with
                                        | (uu____5236,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5261,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5052 in
                   (match uu____5031 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5374  ->
                                 match uu____5374 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5411 =
                                         let uu____5412 =
                                           let uu____5422 =
                                             let uu____5426 =
                                               let uu____5429 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5430 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5429, uu____5430) in
                                             [uu____5426] in
                                           (s_body, uu____5422) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5412 in
                                       mk1 uu____5411 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5451 =
                              let uu____5452 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5452] in
                            let uu____5453 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____5451 uu____5453
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____5458 =
                              let uu____5462 =
                                let uu____5463 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5463 in
                              [uu____5462] in
                            let uu____5464 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5458 uu____5464 in
                          let uu____5467 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____5497 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5467, uu____5497)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5511 =
                             let uu____5514 =
                               let uu____5515 =
                                 let uu____5533 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5533,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5515 in
                             mk1 uu____5514 in
                           let uu____5560 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5511, uu____5560))))
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
              let uu____5603 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5603] in
            let uu____5604 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5604 with
            | (x_binders1,e21) ->
                let uu____5612 = infer env e1 in
                (match uu____5612 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5623 = is_C t1 in
                       if uu____5623
                       then
                         let uu___119_5624 = binding in
                         let uu____5625 =
                           let uu____5628 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5628 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_5624.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_5624.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5625;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_5624.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_5624.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_5631 = env in
                       let uu____5632 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_5634 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_5634.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_5634.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5632;
                         subst = (uu___120_5631.subst);
                         tc_const = (uu___120_5631.tc_const)
                       } in
                     let uu____5635 = proceed env1 e21 in
                     (match uu____5635 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_5646 = binding in
                            let uu____5647 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_5646.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_5646.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5647;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_5646.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_5646.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5650 =
                            let uu____5653 =
                              let uu____5654 =
                                let uu____5662 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_5668 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_5668.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_5668.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_5668.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_5668.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5662) in
                              FStar_Syntax_Syntax.Tm_let uu____5654 in
                            mk1 uu____5653 in
                          let uu____5669 =
                            let uu____5672 =
                              let uu____5673 =
                                let uu____5681 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_5687 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_5687.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_5687.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_5687.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_5687.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5681) in
                              FStar_Syntax_Syntax.Tm_let uu____5673 in
                            mk1 uu____5672 in
                          (nm_rec, uu____5650, uu____5669))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_5696 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_5696.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_5696.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_5696.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_5698 = env in
                       let uu____5699 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_5701 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_5701.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_5701.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5699;
                         subst = (uu___126_5698.subst);
                         tc_const = (uu___126_5698.tc_const)
                       } in
                     let uu____5702 = ensure_m env1 e21 in
                     (match uu____5702 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____5719 =
                              let uu____5720 =
                                let uu____5730 =
                                  let uu____5734 =
                                    let uu____5737 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5738 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5737, uu____5738) in
                                  [uu____5734] in
                                (s_e2, uu____5730) in
                              FStar_Syntax_Syntax.Tm_app uu____5720 in
                            mk1 uu____5719 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____5750 =
                              let uu____5751 =
                                let uu____5761 =
                                  let uu____5765 =
                                    let uu____5768 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5768) in
                                  [uu____5765] in
                                (s_e1, uu____5761) in
                              FStar_Syntax_Syntax.Tm_app uu____5751 in
                            mk1 uu____5750 in
                          let uu____5776 =
                            let uu____5777 =
                              let uu____5778 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5778] in
                            FStar_Syntax_Util.abs uu____5777 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____5779 =
                            let uu____5782 =
                              let uu____5783 =
                                let uu____5791 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_5797 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_5797.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_5797.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_5797.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_5797.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5791) in
                              FStar_Syntax_Syntax.Tm_let uu____5783 in
                            mk1 uu____5782 in
                          ((M t2), uu____5776, uu____5779)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5806 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____5806 in
      let uu____5811 = check env e mn in
      match uu____5811 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5821 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5834 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____5834 in
      let uu____5839 = check env e mn in
      match uu____5839 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5849 -> failwith "[check_m]: impossible"
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
        (let uu____5871 =
           let uu____5872 = is_C c in Prims.op_Negation uu____5872 in
         if uu____5871 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____5884 =
           let uu____5885 = FStar_Syntax_Subst.compress c in
           uu____5885.FStar_Syntax_Syntax.n in
         match uu____5884 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5904 = FStar_Syntax_Util.head_and_args wp in
             (match uu____5904 with
              | (wp_head,wp_args) ->
                  ((let uu____5931 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5949 =
                           let uu____5950 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5950 in
                         Prims.op_Negation uu____5949) in
                    if uu____5931 then failwith "mismatch" else ());
                   (let uu____5962 =
                      let uu____5963 =
                        let uu____5973 =
                          FStar_List.map2
                            (fun uu____5992  ->
                               fun uu____5993  ->
                                 match (uu____5992, uu____5993) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6016 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6016
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6019 = print_implicit q in
                                         let uu____6020 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6019 uu____6020)
                                      else ();
                                      (let uu____6022 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6022, q)))) args wp_args in
                        (head1, uu____5973) in
                      FStar_Syntax_Syntax.Tm_app uu____5963 in
                    mk1 uu____5962)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6044 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6044 with
              | (binders_orig,comp1) ->
                  let uu____6049 =
                    let uu____6057 =
                      FStar_List.map
                        (fun uu____6078  ->
                           match uu____6078 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6091 = is_C h in
                               if uu____6091
                               then
                                 let w' =
                                   let uu____6098 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____6098 in
                                 let uu____6099 =
                                   let uu____6103 =
                                     let uu____6107 =
                                       let uu____6110 =
                                         let uu____6111 =
                                           let uu____6112 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6112 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6111 in
                                       (uu____6110, q) in
                                     [uu____6107] in
                                   (w', q) :: uu____6103 in
                                 (w', uu____6099)
                               else
                                 (let x =
                                    let uu____6124 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____6124 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6057 in
                  (match uu____6049 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6154 =
                           let uu____6156 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6156 in
                         FStar_Syntax_Subst.subst_comp uu____6154 comp1 in
                       let app =
                         let uu____6160 =
                           let uu____6161 =
                             let uu____6171 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6181 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6182 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6181, uu____6182)) bvs in
                             (wp, uu____6171) in
                           FStar_Syntax_Syntax.Tm_app uu____6161 in
                         mk1 uu____6160 in
                       let comp3 =
                         let uu____6187 = type_of_comp comp2 in
                         let uu____6188 = is_monadic_comp comp2 in
                         trans_G env uu____6187 uu____6188 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6190,uu____6191) ->
             trans_F_ env e wp
         | uu____6220 -> failwith "impossible trans_F_")
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
            let uu____6225 =
              let uu____6226 = star_type' env h in
              let uu____6229 =
                let uu____6235 =
                  let uu____6238 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6238) in
                [uu____6235] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6226;
                FStar_Syntax_Syntax.effect_args = uu____6229;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6225
          else
            (let uu____6244 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6244)
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
    fun t  -> let uu____6259 = n env.env t in star_type' env uu____6259
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____6273 = n env.env t in check_n env uu____6273
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6286 = n env.env c in
        let uu____6287 = n env.env wp in trans_F_ env uu____6286 uu____6287