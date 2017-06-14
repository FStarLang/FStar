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
            (FStar_Syntax_Syntax.sigelts* FStar_Syntax_Syntax.eff_decl)
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
              let uu___101_83 = a in
              let uu____84 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___101_83.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___101_83.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____84
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____92 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____92
             then
               (d "Elaborating extra WP combinators";
                (let uu____94 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____94))
             else ());
            (let rec collect_binders t =
               let uu____103 =
                 let uu____104 =
                   let uu____107 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____107 in
                 uu____104.FStar_Syntax_Syntax.n in
               match uu____103 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____129) -> t1
                     | uu____136 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____139 = collect_binders rest in
                   FStar_List.append bs uu____139
               | FStar_Syntax_Syntax.Tm_type uu____145 -> []
               | uu____148 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____160 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____160 FStar_Syntax_Util.name_binders in
             (let uu____171 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____171
              then
                let uu____172 =
                  let uu____173 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____173 in
                d uu____172
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____205 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____205 with
                | (sigelt,fv) ->
                    ((let uu____211 =
                        let uu____213 = FStar_ST.read sigelts in sigelt ::
                          uu____213 in
                      FStar_ST.write sigelts uu____211);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____234  ->
                     match uu____234 with
                     | (t,b) ->
                         let uu____241 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____241)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____258 = FStar_Syntax_Syntax.as_implicit true in
                     ((fst t), uu____258)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____271 = FStar_Syntax_Syntax.bv_to_name (fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____271) in
              let uu____272 =
                let uu____284 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let body =
                      let uu____304 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____304 in
                    let uu____307 =
                      let uu____308 =
                        let uu____312 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____313 =
                          let uu____315 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____315] in
                        uu____312 :: uu____313 in
                      FStar_List.append binders uu____308 in
                    FStar_Syntax_Util.abs uu____307 body None in
                  let uu____323 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____324 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____323, uu____324) in
                match uu____284 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____355 =
                        let uu____356 =
                          let uu____366 =
                            let uu____370 =
                              FStar_List.map
                                (fun uu____378  ->
                                   match uu____378 with
                                   | (bv,uu____384) ->
                                       let uu____385 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____386 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____385, uu____386)) binders in
                            let uu____387 =
                              let uu____391 =
                                let uu____394 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____395 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____394, uu____395) in
                              let uu____396 =
                                let uu____400 =
                                  let uu____403 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____403) in
                                [uu____400] in
                              uu____391 :: uu____396 in
                            FStar_List.append uu____370 uu____387 in
                          (fv, uu____366) in
                        FStar_Syntax_Syntax.Tm_app uu____356 in
                      mk1 uu____355 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____272 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____449 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____449 in
                    let ret1 =
                      let uu____457 =
                        let uu____463 =
                          let uu____464 =
                            let uu____467 =
                              let uu____468 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____468 in
                            FStar_Syntax_Syntax.mk_Total uu____467 in
                          FStar_Syntax_Util.lcomp_of_comp uu____464 in
                        FStar_Util.Inl uu____463 in
                      Some uu____457 in
                    let body =
                      let uu____478 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____478 ret1 in
                    let uu____479 =
                      let uu____480 = mk_all_implicit binders in
                      let uu____484 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____480 uu____484 in
                    FStar_Syntax_Util.abs uu____479 body ret1 in
                  let c_pure1 =
                    let uu____499 = mk_lid "pure" in
                    register env1 uu____499 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____504 =
                        let uu____505 =
                          let uu____506 =
                            let uu____510 =
                              let uu____511 =
                                let uu____512 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____512 in
                              FStar_Syntax_Syntax.mk_binder uu____511 in
                            [uu____510] in
                          let uu____513 =
                            let uu____516 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____516 in
                          FStar_Syntax_Util.arrow uu____506 uu____513 in
                        mk_gctx uu____505 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____504 in
                    let r =
                      let uu____518 =
                        let uu____519 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____519 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____518 in
                    let ret1 =
                      let uu____527 =
                        let uu____533 =
                          let uu____534 =
                            let uu____537 =
                              let uu____538 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____538 in
                            FStar_Syntax_Syntax.mk_Total uu____537 in
                          FStar_Syntax_Util.lcomp_of_comp uu____534 in
                        FStar_Util.Inl uu____533 in
                      Some uu____527 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____553 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____556 =
                          let uu____562 =
                            let uu____564 =
                              let uu____565 =
                                let uu____566 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____566
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____565 in
                            [uu____564] in
                          FStar_List.append gamma_as_args uu____562 in
                        FStar_Syntax_Util.mk_app uu____553 uu____556 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____569 =
                      let uu____570 = mk_all_implicit binders in
                      let uu____574 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____570 uu____574 in
                    FStar_Syntax_Util.abs uu____569 outer_body ret1 in
                  let c_app1 =
                    let uu____593 = mk_lid "app" in
                    register env1 uu____593 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____600 =
                        let uu____604 =
                          let uu____605 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____605 in
                        [uu____604] in
                      let uu____606 =
                        let uu____609 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____609 in
                      FStar_Syntax_Util.arrow uu____600 uu____606 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____612 =
                        let uu____613 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____613 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____612 in
                    let ret1 =
                      let uu____621 =
                        let uu____627 =
                          let uu____628 =
                            let uu____631 =
                              let uu____632 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____632 in
                            FStar_Syntax_Syntax.mk_Total uu____631 in
                          FStar_Syntax_Util.lcomp_of_comp uu____628 in
                        FStar_Util.Inl uu____627 in
                      Some uu____621 in
                    let uu____641 =
                      let uu____642 = mk_all_implicit binders in
                      let uu____646 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____642 uu____646 in
                    let uu____664 =
                      let uu____665 =
                        let uu____671 =
                          let uu____673 =
                            let uu____676 =
                              let uu____682 =
                                let uu____684 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____684] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____682 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____676 in
                          let uu____685 =
                            let uu____689 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____689] in
                          uu____673 :: uu____685 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____671 in
                      FStar_Syntax_Util.mk_app c_app1 uu____665 in
                    FStar_Syntax_Util.abs uu____641 uu____664 ret1 in
                  let c_lift11 =
                    let uu____693 = mk_lid "lift1" in
                    register env1 uu____693 c_lift1 in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____701 =
                        let uu____705 =
                          let uu____706 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____706 in
                        let uu____707 =
                          let uu____709 =
                            let uu____710 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____710 in
                          [uu____709] in
                        uu____705 :: uu____707 in
                      let uu____711 =
                        let uu____714 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____714 in
                      FStar_Syntax_Util.arrow uu____701 uu____711 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____717 =
                        let uu____718 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____718 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____717 in
                    let a2 =
                      let uu____720 =
                        let uu____721 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____721 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____720 in
                    let ret1 =
                      let uu____729 =
                        let uu____735 =
                          let uu____736 =
                            let uu____739 =
                              let uu____740 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____740 in
                            FStar_Syntax_Syntax.mk_Total uu____739 in
                          FStar_Syntax_Util.lcomp_of_comp uu____736 in
                        FStar_Util.Inl uu____735 in
                      Some uu____729 in
                    let uu____749 =
                      let uu____750 = mk_all_implicit binders in
                      let uu____754 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____750 uu____754 in
                    let uu____776 =
                      let uu____777 =
                        let uu____783 =
                          let uu____785 =
                            let uu____788 =
                              let uu____794 =
                                let uu____796 =
                                  let uu____799 =
                                    let uu____805 =
                                      let uu____807 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____807] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____805 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____799 in
                                let uu____808 =
                                  let uu____812 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____812] in
                                uu____796 :: uu____808 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____794 in
                            FStar_Syntax_Util.mk_app c_app1 uu____788 in
                          let uu____815 =
                            let uu____819 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____819] in
                          uu____785 :: uu____815 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____783 in
                      FStar_Syntax_Util.mk_app c_app1 uu____777 in
                    FStar_Syntax_Util.abs uu____749 uu____776 ret1 in
                  let c_lift21 =
                    let uu____823 = mk_lid "lift2" in
                    register env1 uu____823 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____830 =
                        let uu____834 =
                          let uu____835 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____835 in
                        [uu____834] in
                      let uu____836 =
                        let uu____839 =
                          let uu____840 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____840 in
                        FStar_Syntax_Syntax.mk_Total uu____839 in
                      FStar_Syntax_Util.arrow uu____830 uu____836 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____849 =
                        let uu____855 =
                          let uu____856 =
                            let uu____859 =
                              let uu____860 =
                                let uu____861 =
                                  let uu____865 =
                                    let uu____866 =
                                      FStar_Syntax_Syntax.bv_to_name t1 in
                                    FStar_Syntax_Syntax.null_binder uu____866 in
                                  [uu____865] in
                                let uu____867 =
                                  let uu____870 =
                                    FStar_Syntax_Syntax.bv_to_name t2 in
                                  FStar_Syntax_Syntax.mk_GTotal uu____870 in
                                FStar_Syntax_Util.arrow uu____861 uu____867 in
                              mk_ctx uu____860 in
                            FStar_Syntax_Syntax.mk_Total uu____859 in
                          FStar_Syntax_Util.lcomp_of_comp uu____856 in
                        FStar_Util.Inl uu____855 in
                      Some uu____849 in
                    let e1 =
                      let uu____880 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____880 in
                    let body =
                      let uu____882 =
                        let uu____883 =
                          let uu____887 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____887] in
                        FStar_List.append gamma uu____883 in
                      let uu____890 =
                        let uu____891 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____894 =
                          let uu____900 =
                            let uu____901 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____901 in
                          let uu____902 = args_of_binders1 gamma in uu____900
                            :: uu____902 in
                        FStar_Syntax_Util.mk_app uu____891 uu____894 in
                      FStar_Syntax_Util.abs uu____882 uu____890 ret1 in
                    let uu____904 =
                      let uu____905 = mk_all_implicit binders in
                      let uu____909 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____905 uu____909 in
                    FStar_Syntax_Util.abs uu____904 body ret1 in
                  let c_push1 =
                    let uu____926 = mk_lid "push" in
                    register env1 uu____926 c_push in
                  let ret_tot_wp_a =
                    let uu____934 =
                      let uu____940 =
                        let uu____941 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____941 in
                      FStar_Util.Inl uu____940 in
                    Some uu____934 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____972 =
                        let uu____973 =
                          let uu____983 = args_of_binders1 binders in
                          (c, uu____983) in
                        FStar_Syntax_Syntax.Tm_app uu____973 in
                      mk1 uu____972
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____991 =
                        let uu____992 =
                          let uu____996 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____997 =
                            let uu____999 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____999] in
                          uu____996 :: uu____997 in
                        let uu____1000 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____992 uu____1000 in
                      FStar_Syntax_Syntax.mk_Total uu____991 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____1004 =
                      let uu____1005 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1005 in
                    let uu____1011 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____1013 =
                        let uu____1016 =
                          let uu____1022 =
                            let uu____1024 =
                              let uu____1027 =
                                let uu____1033 =
                                  let uu____1034 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1034 in
                                [uu____1033] in
                              FStar_Syntax_Util.mk_app l_ite uu____1027 in
                            [uu____1024] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1022 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1016 in
                      FStar_Syntax_Util.ascribe uu____1013
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____1004 uu____1011
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1059 = mk_lid "wp_if_then_else" in
                    register env1 uu____1059 wp_if_then_else in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1 in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q" None
                        FStar_Syntax_Util.ktype in
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1")) None in
                    let body =
                      let uu____1070 =
                        let uu____1076 =
                          let uu____1078 =
                            let uu____1081 =
                              let uu____1087 =
                                let uu____1089 =
                                  let uu____1092 =
                                    let uu____1098 =
                                      let uu____1099 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1099 in
                                    [uu____1098] in
                                  FStar_Syntax_Util.mk_app l_and uu____1092 in
                                [uu____1089] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1087 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1081 in
                          let uu____1104 =
                            let uu____1108 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1108] in
                          uu____1078 :: uu____1104 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1076 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1070 in
                    let uu____1111 =
                      let uu____1112 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1112 in
                    FStar_Syntax_Util.abs uu____1111 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1119 = mk_lid "wp_assert" in
                    register env1 uu____1119 wp_assert in
                  let wp_assert2 = mk_generic_app wp_assert1 in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q" None
                        FStar_Syntax_Util.ktype in
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1")) None in
                    let body =
                      let uu____1130 =
                        let uu____1136 =
                          let uu____1138 =
                            let uu____1141 =
                              let uu____1147 =
                                let uu____1149 =
                                  let uu____1152 =
                                    let uu____1158 =
                                      let uu____1159 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1159 in
                                    [uu____1158] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1152 in
                                [uu____1149] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1147 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1141 in
                          let uu____1164 =
                            let uu____1168 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1168] in
                          uu____1138 :: uu____1164 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1136 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1130 in
                    let uu____1171 =
                      let uu____1172 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1172 in
                    FStar_Syntax_Util.abs uu____1171 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1179 = mk_lid "wp_assume" in
                    register env1 uu____1179 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1188 =
                        let uu____1192 =
                          let uu____1193 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1193 in
                        [uu____1192] in
                      let uu____1194 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1188 uu____1194 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1201 =
                        let uu____1207 =
                          let uu____1209 =
                            let uu____1212 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1212 in
                          let uu____1218 =
                            let uu____1222 =
                              let uu____1225 =
                                let uu____1231 =
                                  let uu____1233 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1233] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1231 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1225 in
                            [uu____1222] in
                          uu____1209 :: uu____1218 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1207 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1201 in
                    let uu____1240 =
                      let uu____1241 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1241 in
                    FStar_Syntax_Util.abs uu____1240 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1248 = mk_lid "wp_close" in
                    register env1 uu____1248 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1259 =
                      let uu____1265 =
                        let uu____1266 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1266 in
                      FStar_Util.Inl uu____1265 in
                    Some uu____1259 in
                  let ret_gtot_type =
                    let uu____1286 =
                      let uu____1292 =
                        let uu____1293 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1293 in
                      FStar_Util.Inl uu____1292 in
                    Some uu____1286 in
                  let mk_forall1 x body =
                    let uu____1313 =
                      let uu____1316 =
                        let uu____1317 =
                          let uu____1327 =
                            let uu____1329 =
                              let uu____1330 =
                                let uu____1331 =
                                  let uu____1332 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1332] in
                                FStar_Syntax_Util.abs uu____1331 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1330 in
                            [uu____1329] in
                          (FStar_Syntax_Util.tforall, uu____1327) in
                        FStar_Syntax_Syntax.Tm_app uu____1317 in
                      FStar_Syntax_Syntax.mk uu____1316 in
                    uu____1313 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1346 =
                      let uu____1347 = FStar_Syntax_Subst.compress t in
                      uu____1347.FStar_Syntax_Syntax.n in
                    match uu____1346 with
                    | FStar_Syntax_Syntax.Tm_type uu____1350 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1365  ->
                              match uu____1365 with
                              | (b,uu____1369) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1370 -> true in
                  let rec is_monotonic t =
                    let uu____1375 =
                      let uu____1376 = FStar_Syntax_Subst.compress t in
                      uu____1376.FStar_Syntax_Syntax.n in
                    match uu____1375 with
                    | FStar_Syntax_Syntax.Tm_type uu____1379 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1394  ->
                              match uu____1394 with
                              | (b,uu____1398) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1399 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1451 =
                      let uu____1452 = FStar_Syntax_Subst.compress t1 in
                      uu____1452.FStar_Syntax_Syntax.n in
                    match uu____1451 with
                    | FStar_Syntax_Syntax.Tm_type uu____1455 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1458);
                                      FStar_Syntax_Syntax.tk = uu____1459;
                                      FStar_Syntax_Syntax.pos = uu____1460;
                                      FStar_Syntax_Syntax.vars = uu____1461;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1484 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1484
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1487 =
                              let uu____1490 =
                                let uu____1496 =
                                  let uu____1497 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1497 in
                                [uu____1496] in
                              FStar_Syntax_Util.mk_app x uu____1490 in
                            let uu____1498 =
                              let uu____1501 =
                                let uu____1507 =
                                  let uu____1508 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1508 in
                                [uu____1507] in
                              FStar_Syntax_Util.mk_app y uu____1501 in
                            mk_rel1 b uu____1487 uu____1498 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1513 =
                               let uu____1514 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1517 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1514 uu____1517 in
                             let uu____1520 =
                               let uu____1521 =
                                 let uu____1524 =
                                   let uu____1530 =
                                     let uu____1531 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1531 in
                                   [uu____1530] in
                                 FStar_Syntax_Util.mk_app x uu____1524 in
                               let uu____1532 =
                                 let uu____1535 =
                                   let uu____1541 =
                                     let uu____1542 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1542 in
                                   [uu____1541] in
                                 FStar_Syntax_Util.mk_app y uu____1535 in
                               mk_rel1 b uu____1521 uu____1532 in
                             FStar_Syntax_Util.mk_imp uu____1513 uu____1520 in
                           let uu____1543 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1543)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1546);
                                      FStar_Syntax_Syntax.tk = uu____1547;
                                      FStar_Syntax_Syntax.pos = uu____1548;
                                      FStar_Syntax_Syntax.vars = uu____1549;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1572 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1572
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1575 =
                              let uu____1578 =
                                let uu____1584 =
                                  let uu____1585 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1585 in
                                [uu____1584] in
                              FStar_Syntax_Util.mk_app x uu____1578 in
                            let uu____1586 =
                              let uu____1589 =
                                let uu____1595 =
                                  let uu____1596 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1596 in
                                [uu____1595] in
                              FStar_Syntax_Util.mk_app y uu____1589 in
                            mk_rel1 b uu____1575 uu____1586 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1601 =
                               let uu____1602 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1605 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1602 uu____1605 in
                             let uu____1608 =
                               let uu____1609 =
                                 let uu____1612 =
                                   let uu____1618 =
                                     let uu____1619 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1619 in
                                   [uu____1618] in
                                 FStar_Syntax_Util.mk_app x uu____1612 in
                               let uu____1620 =
                                 let uu____1623 =
                                   let uu____1629 =
                                     let uu____1630 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1630 in
                                   [uu____1629] in
                                 FStar_Syntax_Util.mk_app y uu____1623 in
                               mk_rel1 b uu____1609 uu____1620 in
                             FStar_Syntax_Util.mk_imp uu____1601 uu____1608 in
                           let uu____1631 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1631)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___102_1652 = t1 in
                          let uu____1653 =
                            let uu____1654 =
                              let uu____1662 =
                                let uu____1663 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1663 in
                              ([binder], uu____1662) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1654 in
                          {
                            FStar_Syntax_Syntax.n = uu____1653;
                            FStar_Syntax_Syntax.tk =
                              (uu___102_1652.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___102_1652.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___102_1652.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1675 ->
                        failwith "unhandled arrow"
                    | uu____1683 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
                  let stronger =
                    let wp1 = FStar_Syntax_Syntax.gen_bv "wp1" None wp_a1 in
                    let wp2 = FStar_Syntax_Syntax.gen_bv "wp2" None wp_a1 in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] env1 t in
                      let uu____1698 =
                        let uu____1699 = FStar_Syntax_Subst.compress t1 in
                        uu____1699.FStar_Syntax_Syntax.n in
                      match uu____1698 with
                      | FStar_Syntax_Syntax.Tm_type uu____1702 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1719 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1719
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1734 =
                                let uu____1735 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1735 i in
                              FStar_Syntax_Syntax.fvar uu____1734
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1759 =
                            let uu____1763 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1768  ->
                                     match uu____1768 with
                                     | (t2,q) ->
                                         let uu____1773 = project i x in
                                         let uu____1774 = project i y in
                                         mk_stronger t2 uu____1773 uu____1774)
                                args in
                            match uu____1763 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1759 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1791);
                                      FStar_Syntax_Syntax.tk = uu____1792;
                                      FStar_Syntax_Syntax.pos = uu____1793;
                                      FStar_Syntax_Syntax.vars = uu____1794;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1816  ->
                                   match uu____1816 with
                                   | (bv,q) ->
                                       let uu____1821 =
                                         let uu____1822 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1822 in
                                       FStar_Syntax_Syntax.gen_bv uu____1821
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1826 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1826) bvs in
                          let body =
                            let uu____1828 = FStar_Syntax_Util.mk_app x args in
                            let uu____1829 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1828 uu____1829 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1834);
                                      FStar_Syntax_Syntax.tk = uu____1835;
                                      FStar_Syntax_Syntax.pos = uu____1836;
                                      FStar_Syntax_Syntax.vars = uu____1837;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1859  ->
                                   match uu____1859 with
                                   | (bv,q) ->
                                       let uu____1864 =
                                         let uu____1865 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1865 in
                                       FStar_Syntax_Syntax.gen_bv uu____1864
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1869 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1869) bvs in
                          let body =
                            let uu____1871 = FStar_Syntax_Util.mk_app x args in
                            let uu____1872 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1871 uu____1872 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1875 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1877 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1878 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1879 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1877 uu____1878 uu____1879 in
                    let uu____1880 =
                      let uu____1881 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1881 in
                    FStar_Syntax_Util.abs uu____1880 body ret_tot_type in
                  let stronger1 =
                    let uu____1896 = mk_lid "stronger" in
                    register env1 uu____1896 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1902 = FStar_Util.prefix gamma in
                    match uu____1902 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1928 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1928 in
                          let uu____1931 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1931 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1939 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1939 in
                              let guard_free1 =
                                let uu____1946 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1946 in
                              let pat =
                                let uu____1950 =
                                  let uu____1956 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1956] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1950 in
                              let pattern_guarded_body =
                                let uu____1960 =
                                  let uu____1961 =
                                    let uu____1966 =
                                      let uu____1967 =
                                        let uu____1974 =
                                          let uu____1976 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1976] in
                                        [uu____1974] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1967 in
                                    (body, uu____1966) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1961 in
                                mk1 uu____1960 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1979 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1982 =
                            let uu____1983 =
                              let uu____1984 =
                                let uu____1985 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1988 =
                                  let uu____1994 = args_of_binders1 wp_args in
                                  let uu____1996 =
                                    let uu____1998 =
                                      let uu____1999 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1999 in
                                    [uu____1998] in
                                  FStar_List.append uu____1994 uu____1996 in
                                FStar_Syntax_Util.mk_app uu____1985
                                  uu____1988 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1984 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1983 in
                          FStar_Syntax_Util.abs gamma uu____1982
                            ret_gtot_type in
                        let uu____2000 =
                          let uu____2001 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2001 in
                        FStar_Syntax_Util.abs uu____2000 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2008 = mk_lid "wp_ite" in
                    register env1 uu____2008 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2014 = FStar_Util.prefix gamma in
                    match uu____2014 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2038 =
                            let uu____2039 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2042 =
                              let uu____2048 =
                                let uu____2049 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2049 in
                              [uu____2048] in
                            FStar_Syntax_Util.mk_app uu____2039 uu____2042 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2038 in
                        let uu____2050 =
                          let uu____2051 =
                            let uu____2055 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2055 gamma in
                          FStar_List.append binders uu____2051 in
                        FStar_Syntax_Util.abs uu____2050 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2064 = mk_lid "null_wp" in
                    register env1 uu____2064 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2073 =
                        let uu____2079 =
                          let uu____2081 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2082 =
                            let uu____2084 =
                              let uu____2087 =
                                let uu____2093 =
                                  let uu____2094 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2094 in
                                [uu____2093] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2087 in
                            let uu____2095 =
                              let uu____2099 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2099] in
                            uu____2084 :: uu____2095 in
                          uu____2081 :: uu____2082 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2079 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2073 in
                    let uu____2102 =
                      let uu____2103 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2103 in
                    FStar_Syntax_Util.abs uu____2102 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2110 = mk_lid "wp_trivial" in
                    register env1 uu____2110 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2115 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2115
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2120 =
                      let uu____2122 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2122 in
                    let uu____2127 =
                      let uu___103_2128 = ed in
                      let uu____2129 =
                        let uu____2130 = c wp_if_then_else2 in
                        ([], uu____2130) in
                      let uu____2132 =
                        let uu____2133 = c wp_ite2 in ([], uu____2133) in
                      let uu____2135 =
                        let uu____2136 = c stronger2 in ([], uu____2136) in
                      let uu____2138 =
                        let uu____2139 = c wp_close2 in ([], uu____2139) in
                      let uu____2141 =
                        let uu____2142 = c wp_assert2 in ([], uu____2142) in
                      let uu____2144 =
                        let uu____2145 = c wp_assume2 in ([], uu____2145) in
                      let uu____2147 =
                        let uu____2148 = c null_wp2 in ([], uu____2148) in
                      let uu____2150 =
                        let uu____2151 = c wp_trivial2 in ([], uu____2151) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_2128.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_2128.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_2128.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_2128.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_2128.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_2128.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_2128.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2129;
                        FStar_Syntax_Syntax.ite_wp = uu____2132;
                        FStar_Syntax_Syntax.stronger = uu____2135;
                        FStar_Syntax_Syntax.close_wp = uu____2138;
                        FStar_Syntax_Syntax.assert_p = uu____2141;
                        FStar_Syntax_Syntax.assume_p = uu____2144;
                        FStar_Syntax_Syntax.null_wp = uu____2147;
                        FStar_Syntax_Syntax.trivial = uu____2150;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_2128.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_2128.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_2128.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_2128.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2120, uu____2127)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_2163 = dmff_env in
      {
        env = env';
        subst = (uu___104_2163.subst);
        tc_const = (uu___104_2163.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2176 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2188 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___90_2198  ->
    match uu___90_2198 with
    | FStar_Syntax_Syntax.Total (t,uu____2200) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___89_2209  ->
                match uu___89_2209 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2210 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2212 =
          let uu____2213 =
            let uu____2214 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2214 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2213 in
        failwith uu____2212
    | FStar_Syntax_Syntax.GTotal uu____2215 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___91_2223  ->
    match uu___91_2223 with
    | N t ->
        let uu____2225 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2225
    | M t ->
        let uu____2227 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2227
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2231,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2233;
                      FStar_Syntax_Syntax.pos = uu____2234;
                      FStar_Syntax_Syntax.vars = uu____2235;_})
        -> nm_of_comp n2
    | uu____2246 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2258 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2258 with | M uu____2259 -> true | N uu____2260 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2264 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2274 =
        let uu____2278 =
          let uu____2279 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2279 in
        [uu____2278] in
      let uu____2280 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2274 uu____2280 in
    let uu____2283 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2283
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
          (let uu____2318 =
             let uu____2326 =
               let uu____2330 =
                 let uu____2333 =
                   let uu____2334 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2334 in
                 let uu____2335 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2333, uu____2335) in
               [uu____2330] in
             let uu____2340 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2326, uu____2340) in
           FStar_Syntax_Syntax.Tm_arrow uu____2318)
and star_type':
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk1 x = FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk1 in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2369) ->
          let binders1 =
            FStar_List.map
              (fun uu____2388  ->
                 match uu____2388 with
                 | (bv,aqual) ->
                     let uu____2395 =
                       let uu___105_2396 = bv in
                       let uu____2397 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_2396.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_2396.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2397
                       } in
                     (uu____2395, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2400,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2402);
                             FStar_Syntax_Syntax.tk = uu____2403;
                             FStar_Syntax_Syntax.pos = uu____2404;
                             FStar_Syntax_Syntax.vars = uu____2405;_})
               ->
               let uu____2422 =
                 let uu____2423 =
                   let uu____2431 =
                     let uu____2432 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2432 in
                   (binders1, uu____2431) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2423 in
               mk1 uu____2422
           | uu____2436 ->
               let uu____2437 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2437 with
                | N hn ->
                    let uu____2439 =
                      let uu____2440 =
                        let uu____2448 =
                          let uu____2449 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2449 in
                        (binders1, uu____2448) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2440 in
                    mk1 uu____2439
                | M a ->
                    let uu____2454 =
                      let uu____2455 =
                        let uu____2463 =
                          let uu____2467 =
                            let uu____2471 =
                              let uu____2474 =
                                let uu____2475 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2475 in
                              let uu____2476 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2474, uu____2476) in
                            [uu____2471] in
                          FStar_List.append binders1 uu____2467 in
                        let uu____2483 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2463, uu____2483) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2455 in
                    mk1 uu____2454))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2534 = f x in
                    FStar_Util.string_builder_append strb uu____2534);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2538 = f x1 in
                         FStar_Util.string_builder_append strb uu____2538))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2540 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2541 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2540 uu____2541 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2549 =
              let uu____2550 = FStar_Syntax_Subst.compress ty in
              uu____2550.FStar_Syntax_Syntax.n in
            match uu____2549 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2565 =
                  let uu____2566 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2566 in
                if uu____2565
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2580 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2580 s in
                       let uu____2582 =
                         let uu____2583 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2583 in
                       if uu____2582
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2586 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2586 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2597  ->
                                  match uu____2597 with
                                  | (bv,uu____2603) ->
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
            | uu____2618 ->
                ((let uu____2620 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2620);
                 false) in
          let rec is_valid_application head2 =
            let uu____2625 =
              let uu____2626 = FStar_Syntax_Subst.compress head2 in
              uu____2626.FStar_Syntax_Syntax.n in
            match uu____2625 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.eq2_lid))
                  ||
                  (let uu____2630 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2630)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv when
                is_non_dependent_arrow
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.ty
                  (FStar_List.length args)
                ->
                let res =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Inlining;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                (match res.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_app uu____2645 -> true
                 | uu____2655 ->
                     ((let uu____2657 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2657);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2658 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2659 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2661) ->
                is_valid_application t2
            | uu____2666 -> false in
          let uu____2667 = is_valid_application head1 in
          if uu____2667
          then
            let uu____2668 =
              let uu____2669 =
                let uu____2679 =
                  FStar_List.map
                    (fun uu____2689  ->
                       match uu____2689 with
                       | (t2,qual) ->
                           let uu____2702 = star_type' env t2 in
                           (uu____2702, qual)) args in
                (head1, uu____2679) in
              FStar_Syntax_Syntax.Tm_app uu____2669 in
            mk1 uu____2668
          else
            (let uu____2709 =
               let uu____2710 =
                 let uu____2711 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2711 in
               FStar_Errors.Err uu____2710 in
             raise uu____2709)
      | FStar_Syntax_Syntax.Tm_bvar uu____2712 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2713 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2714 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2715 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2741 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2741 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___108_2747 = env in
                 let uu____2748 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2748;
                   subst = (uu___108_2747.subst);
                   tc_const = (uu___108_2747.tc_const)
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
               ((let uu___109_2765 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_2765.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_2765.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2772 =
            let uu____2773 =
              let uu____2778 = star_type' env t2 in (uu____2778, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2773 in
          mk1 uu____2772
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2816 =
            let uu____2817 =
              let uu____2835 = star_type' env e in
              let uu____2836 =
                let uu____2846 =
                  let uu____2851 = star_type' env t2 in
                  FStar_Util.Inl uu____2851 in
                (uu____2846, None) in
              (uu____2835, uu____2836, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2817 in
          mk1 uu____2816
      | FStar_Syntax_Syntax.Tm_ascribed uu____2873 ->
          let uu____2891 =
            let uu____2892 =
              let uu____2893 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2893 in
            FStar_Errors.Err uu____2892 in
          raise uu____2891
      | FStar_Syntax_Syntax.Tm_refine uu____2894 ->
          let uu____2899 =
            let uu____2900 =
              let uu____2901 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2901 in
            FStar_Errors.Err uu____2900 in
          raise uu____2899
      | FStar_Syntax_Syntax.Tm_uinst uu____2902 ->
          let uu____2907 =
            let uu____2908 =
              let uu____2909 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2909 in
            FStar_Errors.Err uu____2908 in
          raise uu____2907
      | FStar_Syntax_Syntax.Tm_constant uu____2910 ->
          let uu____2911 =
            let uu____2912 =
              let uu____2913 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2913 in
            FStar_Errors.Err uu____2912 in
          raise uu____2911
      | FStar_Syntax_Syntax.Tm_match uu____2914 ->
          let uu____2930 =
            let uu____2931 =
              let uu____2932 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2932 in
            FStar_Errors.Err uu____2931 in
          raise uu____2930
      | FStar_Syntax_Syntax.Tm_let uu____2933 ->
          let uu____2941 =
            let uu____2942 =
              let uu____2943 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2943 in
            FStar_Errors.Err uu____2942 in
          raise uu____2941
      | FStar_Syntax_Syntax.Tm_uvar uu____2944 ->
          let uu____2953 =
            let uu____2954 =
              let uu____2955 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2955 in
            FStar_Errors.Err uu____2954 in
          raise uu____2953
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2956 =
            let uu____2957 =
              let uu____2958 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2958 in
            FStar_Errors.Err uu____2957 in
          raise uu____2956
      | FStar_Syntax_Syntax.Tm_delayed uu____2959 -> failwith "impossible"
let is_monadic uu___93_2992 =
  match uu___93_2992 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3004;
        FStar_Syntax_Syntax.res_typ = uu____3005;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3007;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3024  ->
              match uu___92_3024 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3025 -> false))
  | Some (FStar_Util.Inr (uu____3026,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3039  ->
              match uu___92_3039 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3040 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3044 =
      let uu____3045 = FStar_Syntax_Subst.compress t in
      uu____3045.FStar_Syntax_Syntax.n in
    match uu____3044 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3065 =
            let uu____3066 = FStar_List.hd args in fst uu____3066 in
          is_C uu____3065 in
        if r
        then
          ((let uu____3078 =
              let uu____3079 =
                FStar_List.for_all
                  (fun uu____3082  ->
                     match uu____3082 with | (h,uu____3086) -> is_C h) args in
              Prims.op_Negation uu____3079 in
            if uu____3078 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3090 =
              let uu____3091 =
                FStar_List.for_all
                  (fun uu____3094  ->
                     match uu____3094 with
                     | (h,uu____3098) ->
                         let uu____3099 = is_C h in
                         Prims.op_Negation uu____3099) args in
              Prims.op_Negation uu____3091 in
            if uu____3090 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3113 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3113 with
         | M t1 ->
             ((let uu____3116 = is_C t1 in
               if uu____3116 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3120) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3126) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3132,uu____3133) -> is_C t1
    | uu____3162 -> false
let mk_return:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk1 env t in
        let p = FStar_Syntax_Syntax.gen_bv "p'" None p_type in
        let body =
          let uu____3189 =
            let uu____3190 =
              let uu____3200 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3201 =
                let uu____3205 =
                  let uu____3208 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3208) in
                [uu____3205] in
              (uu____3200, uu____3201) in
            FStar_Syntax_Syntax.Tm_app uu____3190 in
          mk1 uu____3189 in
        let uu____3216 =
          let uu____3217 = FStar_Syntax_Syntax.mk_binder p in [uu____3217] in
        let uu____3218 =
          let uu____3225 =
            let uu____3231 =
              let uu____3232 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3232 in
            FStar_Util.Inl uu____3231 in
          Some uu____3225 in
        FStar_Syntax_Util.abs uu____3216 body uu____3218
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___94_3245  ->
    match uu___94_3245 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3246 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3380 =
          match uu____3380 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3401 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3402 =
                       let uu____3403 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3403 in
                     Prims.op_Negation uu____3402) in
                if uu____3401
                then
                  let uu____3404 =
                    let uu____3405 =
                      let uu____3406 = FStar_Syntax_Print.term_to_string e in
                      let uu____3407 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3408 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3406 uu____3407 uu____3408 in
                    FStar_Errors.Err uu____3405 in
                  raise uu____3404
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3422 = mk_return env t1 s_e in
                     ((M t1), uu____3422, u_e)))
               | (M t1,N t2) ->
                   let uu____3425 =
                     let uu____3426 =
                       let uu____3427 = FStar_Syntax_Print.term_to_string e in
                       let uu____3428 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3429 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3427 uu____3428 uu____3429 in
                     FStar_Errors.Err uu____3426 in
                   raise uu____3425) in
        let ensure_m env1 e2 =
          let strip_m uu___95_3455 =
            match uu___95_3455 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3465 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3476 =
                let uu____3477 =
                  let uu____3480 =
                    let uu____3481 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3481 in
                  (uu____3480, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3477 in
              raise uu____3476
          | M uu____3485 ->
              let uu____3486 = check env1 e2 context_nm in strip_m uu____3486 in
        let uu____3490 =
          let uu____3491 = FStar_Syntax_Subst.compress e in
          uu____3491.FStar_Syntax_Syntax.n in
        match uu____3490 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3497 ->
            let uu____3498 = infer env e in return_if uu____3498
        | FStar_Syntax_Syntax.Tm_name uu____3502 ->
            let uu____3503 = infer env e in return_if uu____3503
        | FStar_Syntax_Syntax.Tm_fvar uu____3507 ->
            let uu____3508 = infer env e in return_if uu____3508
        | FStar_Syntax_Syntax.Tm_abs uu____3512 ->
            let uu____3527 = infer env e in return_if uu____3527
        | FStar_Syntax_Syntax.Tm_constant uu____3531 ->
            let uu____3532 = infer env e in return_if uu____3532
        | FStar_Syntax_Syntax.Tm_app uu____3536 ->
            let uu____3546 = infer env e in return_if uu____3546
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3593) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3599) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3605,uu____3606) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3635 ->
            let uu____3643 =
              let uu____3644 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3644 in
            failwith uu____3643
        | FStar_Syntax_Syntax.Tm_type uu____3648 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3652 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3663 ->
            let uu____3668 =
              let uu____3669 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3669 in
            failwith uu____3668
        | FStar_Syntax_Syntax.Tm_uvar uu____3673 ->
            let uu____3682 =
              let uu____3683 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3683 in
            failwith uu____3682
        | FStar_Syntax_Syntax.Tm_delayed uu____3687 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3711 =
              let uu____3712 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3712 in
            failwith uu____3711
and infer:
  env ->
    FStar_Syntax_Syntax.term ->
      (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env in
      let uu____3734 =
        let uu____3735 = FStar_Syntax_Subst.compress e in
        uu____3735.FStar_Syntax_Syntax.n in
      match uu____3734 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___110_3775 = env in
            let uu____3776 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3776;
              subst = (uu___110_3775.subst);
              tc_const = (uu___110_3775.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3785  ->
                 match uu____3785 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___111_3793 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___111_3793.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___111_3793.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3794 =
            FStar_List.fold_left
              (fun uu____3803  ->
                 fun uu____3804  ->
                   match (uu____3803, uu____3804) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3832 = is_C c in
                       if uu____3832
                       then
                         let xw =
                           let uu____3837 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3837 in
                         let x =
                           let uu___112_3839 = bv in
                           let uu____3840 =
                             let uu____3843 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3843 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___112_3839.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___112_3839.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3840
                           } in
                         let env3 =
                           let uu___113_3845 = env2 in
                           let uu____3846 =
                             let uu____3848 =
                               let uu____3849 =
                                 let uu____3854 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3854) in
                               FStar_Syntax_Syntax.NT uu____3849 in
                             uu____3848 :: (env2.subst) in
                           {
                             env = (uu___113_3845.env);
                             subst = uu____3846;
                             tc_const = (uu___113_3845.tc_const)
                           } in
                         let uu____3855 =
                           let uu____3857 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3858 =
                             let uu____3860 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3860 :: acc in
                           uu____3857 :: uu____3858 in
                         (env3, uu____3855)
                       else
                         (let x =
                            let uu___114_3864 = bv in
                            let uu____3865 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_3864.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_3864.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3865
                            } in
                          let uu____3868 =
                            let uu____3870 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3870 :: acc in
                          (env2, uu____3868))) (env1, []) binders1 in
          (match uu____3794 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3882 =
                 let check_what =
                   let uu____3894 = is_monadic what in
                   if uu____3894 then check_m else check_n in
                 let uu____3903 = check_what env2 body1 in
                 match uu____3903 with
                 | (t,s_body,u_body) ->
                     let uu____3913 =
                       let uu____3914 =
                         let uu____3915 = is_monadic what in
                         if uu____3915 then M t else N t in
                       comp_of_nm uu____3914 in
                     (uu____3913, s_body, u_body) in
               (match uu____3882 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3958 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___96_3960  ->
                                    match uu___96_3960 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3961 -> false)) in
                          if uu____3958
                          then
                            let double_starred_comp =
                              let uu____3969 =
                                let uu____3970 =
                                  let uu____3971 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____3971 in
                                FStar_All.pipe_left double_star uu____3970 in
                              FStar_Syntax_Syntax.mk_Total uu____3969 in
                            let flags =
                              FStar_List.filter
                                (fun uu___97_3976  ->
                                   match uu___97_3976 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3977 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____3978 =
                              let uu____3984 =
                                let uu____3985 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____3985 in
                              FStar_Util.Inl uu____3984 in
                            Some uu____3978
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___115_4005 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___115_4005.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___115_4005.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___115_4005.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4006  ->
                                          let c =
                                            lc.FStar_Syntax_Syntax.comp () in
                                          let result_typ =
                                            star_type' env2
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          FStar_Syntax_Util.set_result_typ c
                                            result_typ)
                                   })))
                      | Some (FStar_Util.Inr (lid,flags)) ->
                          let uu____4023 =
                            let uu____4029 =
                              let uu____4033 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___98_4035  ->
                                        match uu___98_4035 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4036 -> false)) in
                              if uu____4033
                              then
                                let uu____4040 =
                                  FStar_List.filter
                                    (fun uu___99_4042  ->
                                       match uu___99_4042 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4043 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4040)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4029 in
                          Some uu____4023 in
                    let uu____4055 =
                      let comp1 =
                        let uu____4067 = is_monadic what in
                        let uu____4068 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4067 uu____4068 in
                      let uu____4069 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4069,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4055 with
                     | (u_body1,u_what) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           mk1
                             (FStar_Syntax_Syntax.Tm_abs
                                (s_binders1, s_body1, s_what)) in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           mk1
                             (FStar_Syntax_Syntax.Tm_abs
                                (u_binders2, u_body2, u_what)) in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.ty = uu____4147;
                FStar_Syntax_Syntax.p = uu____4148;_};
            FStar_Syntax_Syntax.fv_delta = uu____4149;
            FStar_Syntax_Syntax.fv_qual = uu____4150;_}
          ->
          let uu____4156 =
            let uu____4159 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4159 in
          (match uu____4156 with
           | (uu____4175,t) ->
               let uu____4177 = let uu____4178 = normalize1 t in N uu____4178 in
               (uu____4177, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4195 = check_n env head1 in
          (match uu____4195 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4209 =
                   let uu____4210 = FStar_Syntax_Subst.compress t in
                   uu____4210.FStar_Syntax_Syntax.n in
                 match uu____4209 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4213 -> true
                 | uu____4221 -> false in
               let rec flatten1 t =
                 let uu____4233 =
                   let uu____4234 = FStar_Syntax_Subst.compress t in
                   uu____4234.FStar_Syntax_Syntax.n in
                 match uu____4233 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4246);
                                FStar_Syntax_Syntax.tk = uu____4247;
                                FStar_Syntax_Syntax.pos = uu____4248;
                                FStar_Syntax_Syntax.vars = uu____4249;_})
                     when is_arrow t1 ->
                     let uu____4266 = flatten1 t1 in
                     (match uu____4266 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4318,uu____4319)
                     -> flatten1 e1
                 | uu____4348 ->
                     let uu____4349 =
                       let uu____4350 =
                         let uu____4351 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4351 in
                       FStar_Errors.Err uu____4350 in
                     raise uu____4349 in
               let uu____4359 = flatten1 t_head in
               (match uu____4359 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4411 =
                          let uu____4412 =
                            let uu____4413 = FStar_Util.string_of_int n1 in
                            let uu____4420 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4431 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4413 uu____4420 uu____4431 in
                          FStar_Errors.Err uu____4412 in
                        raise uu____4411)
                     else ();
                     (let uu____4439 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4439 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4466 args1 =
                            match uu____4466 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4509 =
                                       let uu____4510 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4510.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4509
                                 | (binders3,[]) ->
                                     let uu____4529 =
                                       let uu____4530 =
                                         let uu____4533 =
                                           let uu____4534 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4534 in
                                         FStar_Syntax_Subst.compress
                                           uu____4533 in
                                       uu____4530.FStar_Syntax_Syntax.n in
                                     (match uu____4529 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4550 =
                                            let uu____4551 =
                                              let uu____4552 =
                                                let uu____4560 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4560) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4552 in
                                            mk1 uu____4551 in
                                          N uu____4550
                                      | uu____4564 -> failwith "wat?")
                                 | ([],uu____4565::uu____4566) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4591)::binders3,(arg,uu____4594)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4628 = FStar_List.splitAt n' binders1 in
                          (match uu____4628 with
                           | (binders2,uu____4647) ->
                               let uu____4660 =
                                 let uu____4670 =
                                   FStar_List.map2
                                     (fun uu____4690  ->
                                        fun uu____4691  ->
                                          match (uu____4690, uu____4691) with
                                          | ((bv,uu____4708),(arg,q)) ->
                                              let uu____4715 =
                                                let uu____4716 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4716.FStar_Syntax_Syntax.n in
                                              (match uu____4715 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4726 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4739 ->
                                                   let uu____4740 =
                                                     check_n env arg in
                                                   (match uu____4740 with
                                                    | (uu____4751,s_arg,u_arg)
                                                        ->
                                                        let uu____4754 =
                                                          let uu____4758 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4758
                                                          then
                                                            let uu____4762 =
                                                              let uu____4765
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4765, q) in
                                                            [uu____4762;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4754))))
                                     binders2 args in
                                 FStar_List.split uu____4670 in
                               (match uu____4660 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4812 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4818 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4812, uu____4818)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4867) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4873) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4879,uu____4880) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4910 = let uu____4911 = env.tc_const c in N uu____4911 in
          (uu____4910, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4912 ->
          let uu____4920 =
            let uu____4921 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4921 in
          failwith uu____4920
      | FStar_Syntax_Syntax.Tm_type uu____4925 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4929 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4940 ->
          let uu____4945 =
            let uu____4946 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4946 in
          failwith uu____4945
      | FStar_Syntax_Syntax.Tm_uvar uu____4950 ->
          let uu____4959 =
            let uu____4960 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4960 in
          failwith uu____4959
      | FStar_Syntax_Syntax.Tm_delayed uu____4964 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4988 =
            let uu____4989 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4989 in
          failwith uu____4988
and mk_match:
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term))
          -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos in
          let uu____5027 = check_n env e0 in
          match uu____5027 with
          | (uu____5034,s_e0,u_e0) ->
              let uu____5037 =
                let uu____5055 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5088 = FStar_Syntax_Subst.open_branch b in
                       match uu____5088 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___116_5120 = env in
                             let uu____5121 =
                               let uu____5122 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5122 in
                             {
                               env = uu____5121;
                               subst = (uu___116_5120.subst);
                               tc_const = (uu___116_5120.tc_const)
                             } in
                           let uu____5124 = f env1 body in
                           (match uu____5124 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5173 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5055 in
              (match uu____5037 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5238 = FStar_List.hd nms in
                     match uu____5238 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_5242  ->
                          match uu___100_5242 with
                          | M uu____5243 -> true
                          | uu____5244 -> false) nms in
                   let uu____5245 =
                     let uu____5268 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5320  ->
                              match uu____5320 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5443 =
                                         check env original_body (M t2) in
                                       (match uu____5443 with
                                        | (uu____5466,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5495,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5268 in
                   (match uu____5245 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5614  ->
                                 match uu____5614 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5655 =
                                         let uu____5656 =
                                           let uu____5666 =
                                             let uu____5670 =
                                               let uu____5673 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5674 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5673, uu____5674) in
                                             [uu____5670] in
                                           (s_body, uu____5666) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5656 in
                                       mk1 uu____5655 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5696 =
                              let uu____5697 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5697] in
                            let uu____5698 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5700 =
                              let uu____5707 =
                                let uu____5713 =
                                  let uu____5714 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5714 in
                                FStar_Util.Inl uu____5713 in
                              Some uu____5707 in
                            FStar_Syntax_Util.abs uu____5696 uu____5698
                              uu____5700 in
                          let t1_star =
                            let uu____5728 =
                              let uu____5732 =
                                let uu____5733 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5733 in
                              [uu____5732] in
                            let uu____5734 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5728 uu____5734 in
                          let uu____5737 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5767 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5737, uu____5767)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5781 =
                             let uu____5784 =
                               let uu____5785 =
                                 let uu____5803 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5803,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5785 in
                             mk1 uu____5784 in
                           let uu____5830 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5781, uu____5830))))
and mk_let:
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term))
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term*
                 FStar_Syntax_Syntax.term))
            -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x None e2.FStar_Syntax_Syntax.pos in
            let e1 = binding.FStar_Syntax_Syntax.lbdef in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname in
            let x_binders =
              let uu____5873 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5873] in
            let uu____5874 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5874 with
            | (x_binders1,e21) ->
                let uu____5882 = infer env e1 in
                (match uu____5882 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5893 = is_C t1 in
                       if uu____5893
                       then
                         let uu___117_5894 = binding in
                         let uu____5895 =
                           let uu____5898 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5898 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___117_5894.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___117_5894.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5895;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___117_5894.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___117_5894.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___118_5901 = env in
                       let uu____5902 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5903 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5903.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5903.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5902;
                         subst = (uu___118_5901.subst);
                         tc_const = (uu___118_5901.tc_const)
                       } in
                     let uu____5904 = proceed env1 e21 in
                     (match uu____5904 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___120_5915 = binding in
                            let uu____5916 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_5915.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___120_5915.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5916;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_5915.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___120_5915.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5919 =
                            let uu____5922 =
                              let uu____5923 =
                                let uu____5931 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___121_5936 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5936.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5936.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5936.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5936.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5931) in
                              FStar_Syntax_Syntax.Tm_let uu____5923 in
                            mk1 uu____5922 in
                          let uu____5937 =
                            let uu____5940 =
                              let uu____5941 =
                                let uu____5949 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___122_5954 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_5954.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_5954.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_5954.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_5954.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5949) in
                              FStar_Syntax_Syntax.Tm_let uu____5941 in
                            mk1 uu____5940 in
                          (nm_rec, uu____5919, uu____5937))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___123_5963 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___123_5963.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___123_5963.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___123_5963.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___124_5965 = env in
                       let uu____5966 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_5967 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_5967.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_5967.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5966;
                         subst = (uu___124_5965.subst);
                         tc_const = (uu___124_5965.tc_const)
                       } in
                     let uu____5968 = ensure_m env1 e21 in
                     (match uu____5968 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5985 =
                              let uu____5986 =
                                let uu____5996 =
                                  let uu____6000 =
                                    let uu____6003 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6004 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6003, uu____6004) in
                                  [uu____6000] in
                                (s_e2, uu____5996) in
                              FStar_Syntax_Syntax.Tm_app uu____5986 in
                            mk1 uu____5985 in
                          let s_e22 =
                            let uu____6013 =
                              let uu____6020 =
                                let uu____6026 =
                                  let uu____6027 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6027 in
                                FStar_Util.Inl uu____6026 in
                              Some uu____6020 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6013 in
                          let body =
                            let uu____6041 =
                              let uu____6042 =
                                let uu____6052 =
                                  let uu____6056 =
                                    let uu____6059 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6059) in
                                  [uu____6056] in
                                (s_e1, uu____6052) in
                              FStar_Syntax_Syntax.Tm_app uu____6042 in
                            mk1 uu____6041 in
                          let uu____6067 =
                            let uu____6068 =
                              let uu____6069 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6069] in
                            let uu____6070 =
                              let uu____6077 =
                                let uu____6083 =
                                  let uu____6084 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6084 in
                                FStar_Util.Inl uu____6083 in
                              Some uu____6077 in
                            FStar_Syntax_Util.abs uu____6068 body uu____6070 in
                          let uu____6095 =
                            let uu____6098 =
                              let uu____6099 =
                                let uu____6107 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___126_6112 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_6112.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_6112.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_6112.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_6112.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6107) in
                              FStar_Syntax_Syntax.Tm_let uu____6099 in
                            mk1 uu____6098 in
                          ((M t2), uu____6067, uu____6095)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6121 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6121 in
      let uu____6126 = check env e mn in
      match uu____6126 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6136 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6149 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6149 in
      let uu____6154 = check env e mn in
      match uu____6154 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6164 -> failwith "[check_m]: impossible"
and comp_of_nm: nm_ -> FStar_Syntax_Syntax.comp =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t
and mk_M: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      {
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid;
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
        (let uu____6186 =
           let uu____6187 = is_C c in Prims.op_Negation uu____6187 in
         if uu____6186 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6199 =
           let uu____6200 = FStar_Syntax_Subst.compress c in
           uu____6200.FStar_Syntax_Syntax.n in
         match uu____6199 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6219 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6219 with
              | (wp_head,wp_args) ->
                  ((let uu____6246 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6263 =
                           let uu____6264 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6264 in
                         Prims.op_Negation uu____6263) in
                    if uu____6246 then failwith "mismatch" else ());
                   (let uu____6276 =
                      let uu____6277 =
                        let uu____6287 =
                          FStar_List.map2
                            (fun uu____6297  ->
                               fun uu____6298  ->
                                 match (uu____6297, uu____6298) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6321 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6321
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6324 = print_implicit q in
                                         let uu____6325 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6324 uu____6325)
                                      else ();
                                      (let uu____6327 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6327, q)))) args wp_args in
                        (head1, uu____6287) in
                      FStar_Syntax_Syntax.Tm_app uu____6277 in
                    mk1 uu____6276)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6349 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6349 with
              | (binders_orig,comp1) ->
                  let uu____6354 =
                    let uu____6362 =
                      FStar_List.map
                        (fun uu____6376  ->
                           match uu____6376 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6389 = is_C h in
                               if uu____6389
                               then
                                 let w' =
                                   let uu____6396 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6396 in
                                 let uu____6397 =
                                   let uu____6401 =
                                     let uu____6405 =
                                       let uu____6408 =
                                         let uu____6409 =
                                           let uu____6410 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6410 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6409 in
                                       (uu____6408, q) in
                                     [uu____6405] in
                                   (w', q) :: uu____6401 in
                                 (w', uu____6397)
                               else
                                 (let x =
                                    let uu____6422 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6422 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6362 in
                  (match uu____6354 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6452 =
                           let uu____6454 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6454 in
                         FStar_Syntax_Subst.subst_comp uu____6452 comp1 in
                       let app =
                         let uu____6458 =
                           let uu____6459 =
                             let uu____6469 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6476 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6477 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6476, uu____6477)) bvs in
                             (wp, uu____6469) in
                           FStar_Syntax_Syntax.Tm_app uu____6459 in
                         mk1 uu____6458 in
                       let comp3 =
                         let uu____6482 = type_of_comp comp2 in
                         let uu____6483 = is_monadic_comp comp2 in
                         trans_G env uu____6482 uu____6483 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6485,uu____6486) ->
             trans_F_ env e wp
         | uu____6515 -> failwith "impossible trans_F_")
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
            let uu____6520 =
              let uu____6521 = star_type' env h in
              let uu____6524 =
                let uu____6530 =
                  let uu____6533 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6533) in
                [uu____6530] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6521;
                FStar_Syntax_Syntax.effect_args = uu____6524;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6520
          else
            (let uu____6539 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6539)
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
    fun t  -> let uu____6550 = n env.env t in star_type' env uu____6550
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6562 = n env.env t in check_n env uu____6562
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6572 = n env.env c in
        let uu____6573 = n env.env wp in trans_F_ env uu____6572 uu____6573