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
              let uu___102_79 = a in
              let uu____80 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___102_79.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___102_79.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____80
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
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____216 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____216 with
                | (sigelt,fv) ->
                    ((let uu____222 =
                        let uu____224 = FStar_ST.read sigelts in sigelt ::
                          uu____224 in
                      FStar_ST.write sigelts uu____222);
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
                     let uu____269 = FStar_Syntax_Syntax.as_implicit true in
                     ((fst t), uu____269)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____282 = FStar_Syntax_Syntax.bv_to_name (fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____282) in
              let uu____283 =
                let uu____295 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let body =
                      let uu____300 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____300 in
                    let uu____303 =
                      let uu____304 =
                        let uu____308 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____309 =
                          let uu____311 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____311] in
                        uu____308 :: uu____309 in
                      FStar_List.append binders uu____304 in
                    FStar_Syntax_Util.abs uu____303 body None in
                  let uu____314 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____315 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____314, uu____315) in
                match uu____280 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____346 =
                        let uu____347 =
                          let uu____357 =
                            let uu____361 =
                              FStar_List.map
                                (fun uu____369  ->
                                   match uu____369 with
                                   | (bv,uu____375) ->
                                       let uu____376 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____377 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____376, uu____377)) binders in
                            let uu____378 =
                              let uu____382 =
                                let uu____385 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____386 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____385, uu____386) in
                              let uu____387 =
                                let uu____391 =
                                  let uu____394 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____394) in
                                [uu____391] in
                              uu____382 :: uu____387 in
                            FStar_List.append uu____361 uu____378 in
                          (fv, uu____357) in
                        FStar_Syntax_Syntax.Tm_app uu____347 in
                      mk1 uu____346 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____283 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____440 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____440 in
                    let ret1 =
                      let uu____443 =
                        let uu____444 =
                          let uu____447 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____447 in
                        FStar_Syntax_Util.residual_tot uu____444 in
                      Some uu____443 in
                    let body =
                      let uu____449 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____449 ret1 in
                    let uu____450 =
                      let uu____451 = mk_all_implicit binders in
                      let uu____455 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____451 uu____455 in
                    FStar_Syntax_Util.abs uu____450 body ret1 in
                  let c_pure1 =
                    let uu____470 = mk_lid "pure" in
                    register env1 uu____470 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____475 =
                        let uu____476 =
                          let uu____477 =
                            let uu____481 =
                              let uu____482 =
                                let uu____483 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____483 in
                              FStar_Syntax_Syntax.mk_binder uu____482 in
                            [uu____481] in
                          let uu____484 =
                            let uu____487 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____487 in
                          FStar_Syntax_Util.arrow uu____477 uu____484 in
                        mk_gctx uu____476 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____475 in
                    let r =
                      let uu____489 =
                        let uu____490 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____490 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____489 in
                    let ret1 =
                      let uu____493 =
                        let uu____494 =
                          let uu____497 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____497 in
                        FStar_Syntax_Util.residual_tot uu____494 in
                      Some uu____493 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____504 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____507 =
                          let uu____513 =
                            let uu____515 =
                              let uu____516 =
                                let uu____517 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____517
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____516 in
                            [uu____515] in
                          FStar_List.append gamma_as_args uu____513 in
                        FStar_Syntax_Util.mk_app uu____504 uu____507 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____520 =
                      let uu____521 = mk_all_implicit binders in
                      let uu____525 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____521 uu____525 in
                    FStar_Syntax_Util.abs uu____520 outer_body ret1 in
                  let c_app1 =
                    let uu____544 = mk_lid "app" in
                    register env1 uu____544 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____551 =
                        let uu____555 =
                          let uu____556 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____556 in
                        [uu____555] in
                      let uu____557 =
                        let uu____560 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____560 in
                      FStar_Syntax_Util.arrow uu____551 uu____557 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____563 =
                        let uu____564 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____564 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____563 in
                    let ret1 =
                      let uu____567 =
                        let uu____568 =
                          let uu____571 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____571 in
                        FStar_Syntax_Util.residual_tot uu____568 in
                      Some uu____567 in
                    let uu____572 =
                      let uu____573 = mk_all_implicit binders in
                      let uu____577 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____573 uu____577 in
                    let uu____595 =
                      let uu____596 =
                        let uu____602 =
                          let uu____604 =
                            let uu____607 =
                              let uu____613 =
                                let uu____615 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____615] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____613 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____607 in
                          let uu____616 =
                            let uu____620 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____620] in
                          uu____604 :: uu____616 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____602 in
                      FStar_Syntax_Util.mk_app c_app1 uu____596 in
                    FStar_Syntax_Util.abs uu____572 uu____595 ret1 in
                  let c_lift11 =
                    let uu____624 = mk_lid "lift1" in
                    register env1 uu____624 c_lift1 in
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
                      let uu____632 =
                        let uu____636 =
                          let uu____637 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____637 in
                        let uu____638 =
                          let uu____640 =
                            let uu____641 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____641 in
                          [uu____640] in
                        uu____636 :: uu____638 in
                      let uu____642 =
                        let uu____645 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____645 in
                      FStar_Syntax_Util.arrow uu____632 uu____642 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____648 =
                        let uu____649 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____649 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____648 in
                    let a2 =
                      let uu____651 =
                        let uu____652 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____652 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____651 in
                    let ret1 =
                      let uu____655 =
                        let uu____656 =
                          let uu____659 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____659 in
                        FStar_Syntax_Util.residual_tot uu____656 in
                      Some uu____655 in
                    let uu____660 =
                      let uu____661 = mk_all_implicit binders in
                      let uu____665 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____661 uu____665 in
                    let uu____687 =
                      let uu____688 =
                        let uu____694 =
                          let uu____696 =
                            let uu____699 =
                              let uu____705 =
                                let uu____707 =
                                  let uu____710 =
                                    let uu____716 =
                                      let uu____718 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____718] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____716 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____710 in
                                let uu____719 =
                                  let uu____723 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____723] in
                                uu____707 :: uu____719 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____705 in
                            FStar_Syntax_Util.mk_app c_app1 uu____699 in
                          let uu____726 =
                            let uu____730 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____730] in
                          uu____696 :: uu____726 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____694 in
                      FStar_Syntax_Util.mk_app c_app1 uu____688 in
                    FStar_Syntax_Util.abs uu____660 uu____687 ret1 in
                  let c_lift21 =
                    let uu____734 = mk_lid "lift2" in
                    register env1 uu____734 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____741 =
                        let uu____745 =
                          let uu____746 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____746 in
                        [uu____745] in
                      let uu____747 =
                        let uu____750 =
                          let uu____751 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____751 in
                        FStar_Syntax_Syntax.mk_Total uu____750 in
                      FStar_Syntax_Util.arrow uu____741 uu____747 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____755 =
                        let uu____756 =
                          let uu____759 =
                            let uu____760 =
                              let uu____764 =
                                let uu____765 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____765 in
                              [uu____764] in
                            let uu____766 =
                              let uu____769 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____769 in
                            FStar_Syntax_Util.arrow uu____760 uu____766 in
                          mk_ctx uu____759 in
                        FStar_Syntax_Util.residual_tot uu____756 in
                      Some uu____755 in
                    let e1 =
                      let uu____771 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____771 in
                    let body =
                      let uu____773 =
                        let uu____774 =
                          let uu____778 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____778] in
                        FStar_List.append gamma uu____774 in
                      let uu____781 =
                        let uu____782 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____785 =
                          let uu____791 =
                            let uu____792 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____792 in
                          let uu____793 = args_of_binders1 gamma in uu____791
                            :: uu____793 in
                        FStar_Syntax_Util.mk_app uu____782 uu____785 in
                      FStar_Syntax_Util.abs uu____773 uu____781 ret1 in
                    let uu____795 =
                      let uu____796 = mk_all_implicit binders in
                      let uu____800 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____796 uu____800 in
                    FStar_Syntax_Util.abs uu____795 body ret1 in
                  let c_push1 =
                    let uu____817 = mk_lid "push" in
                    register env1 uu____817 c_push in
                  let ret_tot_wp_a =
                    Some (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____840 =
                        let uu____841 =
                          let uu____851 = args_of_binders1 binders in
                          (c, uu____851) in
                        FStar_Syntax_Syntax.Tm_app uu____841 in
                      mk1 uu____840
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____859 =
                        let uu____860 =
                          let uu____864 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____865 =
                            let uu____867 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____867] in
                          uu____864 :: uu____865 in
                        let uu____868 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____860 uu____868 in
                      FStar_Syntax_Syntax.mk_Total uu____859 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____872 =
                      let uu____873 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____873 in
                    let uu____879 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____881 =
                        let uu____884 =
                          let uu____890 =
                            let uu____892 =
                              let uu____895 =
                                let uu____901 =
                                  let uu____902 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____902 in
                                [uu____901] in
                              FStar_Syntax_Util.mk_app l_ite uu____895 in
                            [uu____892] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg uu____890 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____884 in
                      FStar_Syntax_Util.ascribe uu____881
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____872 uu____879
                      (Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____919 = mk_lid "wp_if_then_else" in
                    register env1 uu____919 wp_if_then_else in
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
                      let uu____930 =
                        let uu____936 =
                          let uu____938 =
                            let uu____941 =
                              let uu____947 =
                                let uu____949 =
                                  let uu____952 =
                                    let uu____958 =
                                      let uu____959 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____959 in
                                    [uu____958] in
                                  FStar_Syntax_Util.mk_app l_and uu____952 in
                                [uu____949] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____947 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____941 in
                          let uu____964 =
                            let uu____968 = FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____968] in
                          uu____938 :: uu____964 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____936 in
                      FStar_Syntax_Util.mk_app c_app1 uu____930 in
                    let uu____971 =
                      let uu____972 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____972 in
                    FStar_Syntax_Util.abs uu____971 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____979 = mk_lid "wp_assert" in
                    register env1 uu____979 wp_assert in
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
                      let uu____990 =
                        let uu____996 =
                          let uu____998 =
                            let uu____1001 =
                              let uu____1007 =
                                let uu____1009 =
                                  let uu____1012 =
                                    let uu____1018 =
                                      let uu____1019 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1019 in
                                    [uu____1018] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1012 in
                                [uu____1009] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1007 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1001 in
                          let uu____1024 =
                            let uu____1028 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1028] in
                          uu____998 :: uu____1024 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____996 in
                      FStar_Syntax_Util.mk_app c_app1 uu____990 in
                    let uu____1031 =
                      let uu____1032 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1032 in
                    FStar_Syntax_Util.abs uu____1031 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1039 = mk_lid "wp_assume" in
                    register env1 uu____1039 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1048 =
                        let uu____1052 =
                          let uu____1053 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1053 in
                        [uu____1052] in
                      let uu____1054 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1048 uu____1054 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1061 =
                        let uu____1067 =
                          let uu____1069 =
                            let uu____1072 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1072 in
                          let uu____1078 =
                            let uu____1082 =
                              let uu____1085 =
                                let uu____1091 =
                                  let uu____1093 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1093] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1091 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1085 in
                            [uu____1082] in
                          uu____1069 :: uu____1078 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1067 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1061 in
                    let uu____1100 =
                      let uu____1101 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1101 in
                    FStar_Syntax_Util.abs uu____1100 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1108 = mk_lid "wp_close" in
                    register env1 uu____1108 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1116 =
                      let uu____1117 =
                        let uu____1118 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1118 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1117 in
                    Some uu____1116 in
                  let mk_forall1 x body =
                    let uu____1130 =
                      let uu____1133 =
                        let uu____1134 =
                          let uu____1144 =
                            let uu____1146 =
                              let uu____1147 =
                                let uu____1148 =
                                  let uu____1149 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1149] in
                                FStar_Syntax_Util.abs uu____1148 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1147 in
                            [uu____1146] in
                          (FStar_Syntax_Util.tforall, uu____1144) in
                        FStar_Syntax_Syntax.Tm_app uu____1134 in
                      FStar_Syntax_Syntax.mk uu____1133 in
                    uu____1130 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1163 =
                      let uu____1164 = FStar_Syntax_Subst.compress t in
                      uu____1164.FStar_Syntax_Syntax.n in
                    match uu____1163 with
                    | FStar_Syntax_Syntax.Tm_type uu____1167 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1182  ->
                              match uu____1182 with
                              | (b,uu____1186) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1187 -> true in
                  let rec is_monotonic t =
                    let uu____1192 =
                      let uu____1193 = FStar_Syntax_Subst.compress t in
                      uu____1193.FStar_Syntax_Syntax.n in
                    match uu____1192 with
                    | FStar_Syntax_Syntax.Tm_type uu____1196 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1211  ->
                              match uu____1211 with
                              | (b,uu____1215) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1216 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1268 =
                      let uu____1269 = FStar_Syntax_Subst.compress t1 in
                      uu____1269.FStar_Syntax_Syntax.n in
                    match uu____1268 with
                    | FStar_Syntax_Syntax.Tm_type uu____1272 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1275);
                                      FStar_Syntax_Syntax.tk = uu____1276;
                                      FStar_Syntax_Syntax.pos = uu____1277;
                                      FStar_Syntax_Syntax.vars = uu____1278;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1301 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1301
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1304 =
                              let uu____1307 =
                                let uu____1313 =
                                  let uu____1314 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1314 in
                                [uu____1313] in
                              FStar_Syntax_Util.mk_app x uu____1307 in
                            let uu____1315 =
                              let uu____1318 =
                                let uu____1324 =
                                  let uu____1325 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1325 in
                                [uu____1324] in
                              FStar_Syntax_Util.mk_app y uu____1318 in
                            mk_rel1 b uu____1304 uu____1315 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1330 =
                               let uu____1331 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1334 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1331 uu____1334 in
                             let uu____1337 =
                               let uu____1338 =
                                 let uu____1341 =
                                   let uu____1347 =
                                     let uu____1348 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1348 in
                                   [uu____1347] in
                                 FStar_Syntax_Util.mk_app x uu____1341 in
                               let uu____1349 =
                                 let uu____1352 =
                                   let uu____1358 =
                                     let uu____1359 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1359 in
                                   [uu____1358] in
                                 FStar_Syntax_Util.mk_app y uu____1352 in
                               mk_rel1 b uu____1338 uu____1349 in
                             FStar_Syntax_Util.mk_imp uu____1330 uu____1337 in
                           let uu____1360 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1360)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1363);
                                      FStar_Syntax_Syntax.tk = uu____1364;
                                      FStar_Syntax_Syntax.pos = uu____1365;
                                      FStar_Syntax_Syntax.vars = uu____1366;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1389 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1389
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1392 =
                              let uu____1395 =
                                let uu____1401 =
                                  let uu____1402 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1402 in
                                [uu____1401] in
                              FStar_Syntax_Util.mk_app x uu____1395 in
                            let uu____1403 =
                              let uu____1406 =
                                let uu____1412 =
                                  let uu____1413 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1413 in
                                [uu____1412] in
                              FStar_Syntax_Util.mk_app y uu____1406 in
                            mk_rel1 b uu____1392 uu____1403 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1418 =
                               let uu____1419 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1422 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1419 uu____1422 in
                             let uu____1425 =
                               let uu____1426 =
                                 let uu____1429 =
                                   let uu____1435 =
                                     let uu____1436 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1436 in
                                   [uu____1435] in
                                 FStar_Syntax_Util.mk_app x uu____1429 in
                               let uu____1437 =
                                 let uu____1440 =
                                   let uu____1446 =
                                     let uu____1447 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1447 in
                                   [uu____1446] in
                                 FStar_Syntax_Util.mk_app y uu____1440 in
                               mk_rel1 b uu____1426 uu____1437 in
                             FStar_Syntax_Util.mk_imp uu____1418 uu____1425 in
                           let uu____1448 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1448)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___103_1469 = t1 in
                          let uu____1470 =
                            let uu____1471 =
                              let uu____1479 =
                                let uu____1480 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1480 in
                              ([binder], uu____1479) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1471 in
                          {
                            FStar_Syntax_Syntax.n = uu____1470;
                            FStar_Syntax_Syntax.tk =
                              (uu___103_1469.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___103_1469.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___103_1469.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1492 ->
                        failwith "unhandled arrow"
                    | uu____1500 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1515 =
                        let uu____1516 = FStar_Syntax_Subst.compress t1 in
                        uu____1516.FStar_Syntax_Syntax.n in
                      match uu____1515 with
                      | FStar_Syntax_Syntax.Tm_type uu____1519 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1536 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1536
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1551 =
                                let uu____1552 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1552 i in
                              FStar_Syntax_Syntax.fvar uu____1551
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1576 =
                            let uu____1580 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1585  ->
                                     match uu____1585 with
                                     | (t2,q) ->
                                         let uu____1590 = project i x in
                                         let uu____1591 = project i y in
                                         mk_stronger t2 uu____1590 uu____1591)
                                args in
                            match uu____1580 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1576 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1608);
                                      FStar_Syntax_Syntax.tk = uu____1609;
                                      FStar_Syntax_Syntax.pos = uu____1610;
                                      FStar_Syntax_Syntax.vars = uu____1611;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1633  ->
                                   match uu____1633 with
                                   | (bv,q) ->
                                       let uu____1638 =
                                         let uu____1639 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1639 in
                                       FStar_Syntax_Syntax.gen_bv uu____1638
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1643 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1643) bvs in
                          let body =
                            let uu____1645 = FStar_Syntax_Util.mk_app x args in
                            let uu____1646 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1645 uu____1646 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1651);
                                      FStar_Syntax_Syntax.tk = uu____1652;
                                      FStar_Syntax_Syntax.pos = uu____1653;
                                      FStar_Syntax_Syntax.vars = uu____1654;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1676  ->
                                   match uu____1676 with
                                   | (bv,q) ->
                                       let uu____1681 =
                                         let uu____1682 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1682 in
                                       FStar_Syntax_Syntax.gen_bv uu____1681
                                         None bv.FStar_Syntax_Syntax.sort)
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
                      | uu____1692 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1694 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1695 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1696 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1694 uu____1695 uu____1696 in
                    let uu____1697 =
                      let uu____1698 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1698 in
                    FStar_Syntax_Util.abs uu____1697 body ret_tot_type in
                  let stronger1 =
                    let uu____1713 = mk_lid "stronger" in
                    register env1 uu____1713 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1719 = FStar_Util.prefix gamma in
                    match uu____1719 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1745 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1745 in
                          let uu____1748 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1748 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1756 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1756 in
                              let guard_free1 =
                                let uu____1763 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1763 in
                              let pat =
                                let uu____1767 =
                                  let uu____1773 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1773] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1767 in
                              let pattern_guarded_body =
                                let uu____1777 =
                                  let uu____1778 =
                                    let uu____1783 =
                                      let uu____1784 =
                                        let uu____1791 =
                                          let uu____1793 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1793] in
                                        [uu____1791] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1784 in
                                    (body, uu____1783) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1778 in
                                mk1 uu____1777 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1796 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1799 =
                            let uu____1800 =
                              let uu____1801 =
                                let uu____1802 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1805 =
                                  let uu____1811 = args_of_binders1 wp_args in
                                  let uu____1813 =
                                    let uu____1815 =
                                      let uu____1816 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1816 in
                                    [uu____1815] in
                                  FStar_List.append uu____1811 uu____1813 in
                                FStar_Syntax_Util.mk_app uu____1802
                                  uu____1805 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1801 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1800 in
                          FStar_Syntax_Util.abs gamma uu____1799
                            ret_gtot_type in
                        let uu____1817 =
                          let uu____1818 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1818 in
                        FStar_Syntax_Util.abs uu____1817 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1825 = mk_lid "wp_ite" in
                    register env1 uu____1825 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1831 = FStar_Util.prefix gamma in
                    match uu____1831 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1855 =
                            let uu____1856 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____1859 =
                              let uu____1865 =
                                let uu____1866 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1866 in
                              [uu____1865] in
                            FStar_Syntax_Util.mk_app uu____1856 uu____1859 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1855 in
                        let uu____1867 =
                          let uu____1868 =
                            let uu____1872 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1872 gamma in
                          FStar_List.append binders uu____1868 in
                        FStar_Syntax_Util.abs uu____1867 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1881 = mk_lid "null_wp" in
                    register env1 uu____1881 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____1890 =
                        let uu____1896 =
                          let uu____1898 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____1899 =
                            let uu____1901 =
                              let uu____1904 =
                                let uu____1910 =
                                  let uu____1911 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____1911 in
                                [uu____1910] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1904 in
                            let uu____1912 =
                              let uu____1916 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____1916] in
                            uu____1901 :: uu____1912 in
                          uu____1898 :: uu____1899 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1896 in
                      FStar_Syntax_Util.mk_app stronger2 uu____1890 in
                    let uu____1919 =
                      let uu____1920 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____1920 in
                    FStar_Syntax_Util.abs uu____1919 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____1927 = mk_lid "wp_trivial" in
                    register env1 uu____1927 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____1932 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____1932
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____1937 =
                      let uu____1939 = FStar_ST.read sigelts in
                      FStar_List.rev uu____1939 in
                    let uu____1944 =
                      let uu___104_1945 = ed in
                      let uu____1946 =
                        let uu____1947 = c wp_if_then_else2 in
                        ([], uu____1947) in
                      let uu____1949 =
                        let uu____1950 = c wp_ite2 in ([], uu____1950) in
                      let uu____1952 =
                        let uu____1953 = c stronger2 in ([], uu____1953) in
                      let uu____1955 =
                        let uu____1956 = c wp_close2 in ([], uu____1956) in
                      let uu____1958 =
                        let uu____1959 = c wp_assert2 in ([], uu____1959) in
                      let uu____1961 =
                        let uu____1962 = c wp_assume2 in ([], uu____1962) in
                      let uu____1964 =
                        let uu____1965 = c null_wp2 in ([], uu____1965) in
                      let uu____1967 =
                        let uu____1968 = c wp_trivial2 in ([], uu____1968) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___104_1945.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___104_1945.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___104_1945.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___104_1945.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___104_1945.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___104_1945.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___104_1945.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____1946;
                        FStar_Syntax_Syntax.ite_wp = uu____1949;
                        FStar_Syntax_Syntax.stronger = uu____1952;
                        FStar_Syntax_Syntax.close_wp = uu____1955;
                        FStar_Syntax_Syntax.assert_p = uu____1958;
                        FStar_Syntax_Syntax.assume_p = uu____1961;
                        FStar_Syntax_Syntax.null_wp = uu____1964;
                        FStar_Syntax_Syntax.trivial = uu____1967;
                        FStar_Syntax_Syntax.repr =
                          (uu___104_1945.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___104_1945.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___104_1945.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___104_1945.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____1937, uu____1944)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___105_1983 = dmff_env in
      {
        env = env';
        subst = (uu___105_1983.subst);
        tc_const = (uu___105_1983.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____1997 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2011 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___91_2023  ->
    match uu___91_2023 with
    | FStar_Syntax_Syntax.Total (t,uu____2025) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___90_2034  ->
                match uu___90_2034 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2035 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2037 =
          let uu____2038 =
            let uu____2039 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2039 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2038 in
        failwith uu____2037
    | FStar_Syntax_Syntax.GTotal uu____2040 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___92_2049  ->
    match uu___92_2049 with
    | N t ->
        let uu____2051 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2051
    | M t ->
        let uu____2053 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2053
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2058,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2060;
                      FStar_Syntax_Syntax.pos = uu____2061;
                      FStar_Syntax_Syntax.vars = uu____2062;_})
        -> nm_of_comp n2
    | uu____2073 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2087 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2087 with | M uu____2088 -> true | N uu____2089 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2094 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2105 =
        let uu____2109 =
          let uu____2110 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2110 in
        [uu____2109] in
      let uu____2111 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2105 uu____2111 in
    let uu____2114 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2114
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
          (let uu____2149 =
             let uu____2157 =
               let uu____2161 =
                 let uu____2164 =
                   let uu____2165 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2165 in
                 let uu____2166 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2164, uu____2166) in
               [uu____2161] in
             let uu____2171 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2157, uu____2171) in
           FStar_Syntax_Syntax.Tm_arrow uu____2149)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2200) ->
          let binders1 =
            FStar_List.map
              (fun uu____2219  ->
                 match uu____2219 with
                 | (bv,aqual) ->
                     let uu____2226 =
                       let uu___106_2227 = bv in
                       let uu____2228 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_2227.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_2227.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2228
                       } in
                     (uu____2226, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2231,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2233);
                             FStar_Syntax_Syntax.tk = uu____2234;
                             FStar_Syntax_Syntax.pos = uu____2235;
                             FStar_Syntax_Syntax.vars = uu____2236;_})
               ->
               let uu____2253 =
                 let uu____2254 =
                   let uu____2262 =
                     let uu____2263 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2263 in
                   (binders1, uu____2262) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2254 in
               mk1 uu____2253
           | uu____2267 ->
               let uu____2268 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2268 with
                | N hn ->
                    let uu____2270 =
                      let uu____2271 =
                        let uu____2279 =
                          let uu____2280 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2280 in
                        (binders1, uu____2279) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2271 in
                    mk1 uu____2270
                | M a ->
                    let uu____2285 =
                      let uu____2286 =
                        let uu____2294 =
                          let uu____2298 =
                            let uu____2302 =
                              let uu____2305 =
                                let uu____2306 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2306 in
                              let uu____2307 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2305, uu____2307) in
                            [uu____2302] in
                          FStar_List.append binders1 uu____2298 in
                        let uu____2314 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2294, uu____2314) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2286 in
                    mk1 uu____2285))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2365 = f x in
                    FStar_Util.string_builder_append strb uu____2365);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2369 = f x1 in
                         FStar_Util.string_builder_append strb uu____2369))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2371 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2372 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2371 uu____2372 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2380 =
              let uu____2381 = FStar_Syntax_Subst.compress ty in
              uu____2381.FStar_Syntax_Syntax.n in
            match uu____2380 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2396 =
                  let uu____2397 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2397 in
                if uu____2396
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2411 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2411 s in
                       let uu____2413 =
                         let uu____2414 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2414 in
                       if uu____2413
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2417 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2417 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2428  ->
                                  match uu____2428 with
                                  | (bv,uu____2434) ->
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
            | uu____2449 ->
                ((let uu____2451 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2451);
                 false) in
          let rec is_valid_application head2 =
            let uu____2456 =
              let uu____2457 = FStar_Syntax_Subst.compress head2 in
              uu____2457.FStar_Syntax_Syntax.n in
            match uu____2456 with
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
                  (let uu____2461 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2461)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2476 -> true
                 | uu____2486 ->
                     ((let uu____2488 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2488);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2489 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2490 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2492) ->
                is_valid_application t2
            | uu____2497 -> false in
          let uu____2498 = is_valid_application head1 in
          if uu____2498
          then
            let uu____2499 =
              let uu____2500 =
                let uu____2510 =
                  FStar_List.map
                    (fun uu____2520  ->
                       match uu____2520 with
                       | (t2,qual) ->
                           let uu____2533 = star_type' env t2 in
                           (uu____2533, qual)) args in
                (head1, uu____2510) in
              FStar_Syntax_Syntax.Tm_app uu____2500 in
            mk1 uu____2499
          else
            (let uu____2540 =
               let uu____2541 =
                 let uu____2542 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2542 in
               FStar_Errors.Err uu____2541 in
             raise uu____2540)
      | FStar_Syntax_Syntax.Tm_bvar uu____2543 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2544 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2545 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2546 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2562 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2562 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___109_2568 = env in
                 let uu____2569 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2569;
                   subst = (uu___109_2568.subst);
                   tc_const = (uu___109_2568.tc_const)
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
               ((let uu___110_2586 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___110_2586.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___110_2586.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2593 =
            let uu____2594 =
              let uu____2599 = star_type' env t2 in (uu____2599, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2594 in
          mk1 uu____2593
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2637 =
            let uu____2638 =
              let uu____2656 = star_type' env e in
              let uu____2657 =
                let uu____2667 =
                  let uu____2672 = star_type' env t2 in
                  FStar_Util.Inl uu____2672 in
                (uu____2667, None) in
              (uu____2656, uu____2657, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2638 in
          mk1 uu____2637
      | FStar_Syntax_Syntax.Tm_ascribed uu____2694 ->
          let uu____2712 =
            let uu____2713 =
              let uu____2714 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2714 in
            FStar_Errors.Err uu____2713 in
          raise uu____2712
      | FStar_Syntax_Syntax.Tm_refine uu____2715 ->
          let uu____2720 =
            let uu____2721 =
              let uu____2722 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2722 in
            FStar_Errors.Err uu____2721 in
          raise uu____2720
      | FStar_Syntax_Syntax.Tm_uinst uu____2723 ->
          let uu____2728 =
            let uu____2729 =
              let uu____2730 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2730 in
            FStar_Errors.Err uu____2729 in
          raise uu____2728
      | FStar_Syntax_Syntax.Tm_constant uu____2731 ->
          let uu____2732 =
            let uu____2733 =
              let uu____2734 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2734 in
            FStar_Errors.Err uu____2733 in
          raise uu____2732
      | FStar_Syntax_Syntax.Tm_match uu____2735 ->
          let uu____2751 =
            let uu____2752 =
              let uu____2753 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2753 in
            FStar_Errors.Err uu____2752 in
          raise uu____2751
      | FStar_Syntax_Syntax.Tm_let uu____2754 ->
          let uu____2762 =
            let uu____2763 =
              let uu____2764 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2764 in
            FStar_Errors.Err uu____2763 in
          raise uu____2762
      | FStar_Syntax_Syntax.Tm_uvar uu____2765 ->
          let uu____2774 =
            let uu____2775 =
              let uu____2776 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2776 in
            FStar_Errors.Err uu____2775 in
          raise uu____2774
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2777 =
            let uu____2778 =
              let uu____2779 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2779 in
            FStar_Errors.Err uu____2778 in
          raise uu____2777
      | FStar_Syntax_Syntax.Tm_delayed uu____2780 -> failwith "impossible"
let is_monadic: FStar_Syntax_Syntax.residual_comp option -> Prims.bool =
  fun uu___94_2799  ->
    match uu___94_2799 with
    | None  -> failwith "un-annotated lambda?!"
    | Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___93_2803  ->
                match uu___93_2803 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2804 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2809 =
      let uu____2810 = FStar_Syntax_Subst.compress t in
      uu____2810.FStar_Syntax_Syntax.n in
    match uu____2809 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2830 =
            let uu____2831 = FStar_List.hd args in fst uu____2831 in
          is_C uu____2830 in
        if r
        then
          ((let uu____2843 =
              let uu____2844 =
                FStar_List.for_all
                  (fun uu____2847  ->
                     match uu____2847 with | (h,uu____2851) -> is_C h) args in
              Prims.op_Negation uu____2844 in
            if uu____2843 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2855 =
              let uu____2856 =
                FStar_List.for_all
                  (fun uu____2859  ->
                     match uu____2859 with
                     | (h,uu____2863) ->
                         let uu____2864 = is_C h in
                         Prims.op_Negation uu____2864) args in
              Prims.op_Negation uu____2856 in
            if uu____2855 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2878 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____2878 with
         | M t1 ->
             ((let uu____2881 = is_C t1 in
               if uu____2881 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2885) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2891) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2897,uu____2898) -> is_C t1
    | uu____2927 -> false
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
          let uu____2957 =
            let uu____2958 =
              let uu____2968 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____2969 =
                let uu____2973 =
                  let uu____2976 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____2976) in
                [uu____2973] in
              (uu____2968, uu____2969) in
            FStar_Syntax_Syntax.Tm_app uu____2958 in
          mk1 uu____2957 in
        let uu____2984 =
          let uu____2985 = FStar_Syntax_Syntax.mk_binder p in [uu____2985] in
        FStar_Syntax_Util.abs uu____2984 body
          (Some (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___95_2989  ->
    match uu___95_2989 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____2990 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3124 =
          match uu____3124 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3145 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3146 =
                       let uu____3147 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3147 in
                     Prims.op_Negation uu____3146) in
                if uu____3145
                then
                  let uu____3148 =
                    let uu____3149 =
                      let uu____3150 = FStar_Syntax_Print.term_to_string e in
                      let uu____3151 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3152 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3150 uu____3151 uu____3152 in
                    FStar_Errors.Err uu____3149 in
                  raise uu____3148
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3166 = mk_return env t1 s_e in
                     ((M t1), uu____3166, u_e)))
               | (M t1,N t2) ->
                   let uu____3169 =
                     let uu____3170 =
                       let uu____3171 = FStar_Syntax_Print.term_to_string e in
                       let uu____3172 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3173 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3171 uu____3172 uu____3173 in
                     FStar_Errors.Err uu____3170 in
                   raise uu____3169) in
        let ensure_m env1 e2 =
          let strip_m uu___96_3199 =
            match uu___96_3199 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3209 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3220 =
                let uu____3221 =
                  let uu____3224 =
                    let uu____3225 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3225 in
                  (uu____3224, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3221 in
              raise uu____3220
          | M uu____3229 ->
              let uu____3230 = check env1 e2 context_nm in strip_m uu____3230 in
        let uu____3234 =
          let uu____3235 = FStar_Syntax_Subst.compress e in
          uu____3235.FStar_Syntax_Syntax.n in
        match uu____3234 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3241 ->
            let uu____3242 = infer env e in return_if uu____3242
        | FStar_Syntax_Syntax.Tm_name uu____3246 ->
            let uu____3247 = infer env e in return_if uu____3247
        | FStar_Syntax_Syntax.Tm_fvar uu____3251 ->
            let uu____3252 = infer env e in return_if uu____3252
        | FStar_Syntax_Syntax.Tm_abs uu____3256 ->
            let uu____3266 = infer env e in return_if uu____3266
        | FStar_Syntax_Syntax.Tm_constant uu____3270 ->
            let uu____3271 = infer env e in return_if uu____3271
        | FStar_Syntax_Syntax.Tm_app uu____3275 ->
            let uu____3285 = infer env e in return_if uu____3285
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3332) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3338) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3344,uu____3345) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3374 ->
            let uu____3382 =
              let uu____3383 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3383 in
            failwith uu____3382
        | FStar_Syntax_Syntax.Tm_type uu____3387 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3391 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3402 ->
            let uu____3407 =
              let uu____3408 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3408 in
            failwith uu____3407
        | FStar_Syntax_Syntax.Tm_uvar uu____3412 ->
            let uu____3421 =
              let uu____3422 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3422 in
            failwith uu____3421
        | FStar_Syntax_Syntax.Tm_delayed uu____3426 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3444 =
              let uu____3445 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3445 in
            failwith uu____3444
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
      let uu____3467 =
        let uu____3468 = FStar_Syntax_Subst.compress e in
        uu____3468.FStar_Syntax_Syntax.n in
      match uu____3467 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | Some
                { FStar_Syntax_Syntax.residual_effect = uu____3507;
                  FStar_Syntax_Syntax.residual_typ = None ;
                  FStar_Syntax_Syntax.residual_flags = uu____3508;_}
                -> rc_opt1
            | None  -> rc_opt1
            | Some rc ->
                let uu____3513 =
                  let uu___111_3514 = rc in
                  let uu____3515 =
                    let uu____3519 =
                      let uu____3520 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____3520 in
                    Some uu____3519 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___111_3514.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____3515;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___111_3514.FStar_Syntax_Syntax.residual_flags)
                  } in
                Some uu____3513 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___112_3529 = env in
            let uu____3530 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3530;
              subst = (uu___112_3529.subst);
              tc_const = (uu___112_3529.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3539  ->
                 match uu____3539 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_3547 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_3547.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_3547.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3548 =
            FStar_List.fold_left
              (fun uu____3557  ->
                 fun uu____3558  ->
                   match (uu____3557, uu____3558) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3586 = is_C c in
                       if uu____3586
                       then
                         let xw =
                           let uu____3591 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3591 in
                         let x =
                           let uu___114_3593 = bv in
                           let uu____3594 =
                             let uu____3597 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3597 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_3593.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_3593.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3594
                           } in
                         let env3 =
                           let uu___115_3599 = env2 in
                           let uu____3600 =
                             let uu____3602 =
                               let uu____3603 =
                                 let uu____3608 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3608) in
                               FStar_Syntax_Syntax.NT uu____3603 in
                             uu____3602 :: (env2.subst) in
                           {
                             env = (uu___115_3599.env);
                             subst = uu____3600;
                             tc_const = (uu___115_3599.tc_const)
                           } in
                         let uu____3609 =
                           let uu____3611 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3612 =
                             let uu____3614 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3614 :: acc in
                           uu____3611 :: uu____3612 in
                         (env3, uu____3609)
                       else
                         (let x =
                            let uu___116_3618 = bv in
                            let uu____3619 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_3618.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_3618.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3619
                            } in
                          let uu____3622 =
                            let uu____3624 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3624 :: acc in
                          (env2, uu____3622))) (env1, []) binders1 in
          (match uu____3548 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3636 =
                 let check_what =
                   let uu____3648 = is_monadic rc_opt1 in
                   if uu____3648 then check_m else check_n in
                 let uu____3657 = check_what env2 body1 in
                 match uu____3657 with
                 | (t,s_body,u_body) ->
                     let uu____3667 =
                       let uu____3668 =
                         let uu____3669 = is_monadic rc_opt1 in
                         if uu____3669 then M t else N t in
                       comp_of_nm uu____3668 in
                     (uu____3667, s_body, u_body) in
               (match uu____3636 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_rc_opt =
                      match rc_opt1 with
                      | None  -> None
                      | Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | None  ->
                               let rc1 =
                                 let uu____3688 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___97_3690  ->
                                           match uu___97_3690 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____3691 -> false)) in
                                 if uu____3688
                                 then
                                   let uu____3692 =
                                     FStar_List.filter
                                       (fun uu___98_3694  ->
                                          match uu___98_3694 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____3695 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Syntax_Const.effect_Tot_lid None
                                     uu____3692
                                 else rc in
                               Some rc1
                           | Some rt ->
                               let uu____3704 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___99_3706  ->
                                         match uu___99_3706 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____3707 -> false)) in
                               if uu____3704
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___100_3711  ->
                                        match uu___100_3711 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____3712 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____3713 =
                                   let uu____3714 =
                                     let uu____3718 = double_star rt in
                                     Some uu____3718 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Syntax_Const.effect_Tot_lid
                                     uu____3714 flags in
                                 Some uu____3713
                               else
                                 (let uu____3720 =
                                    let uu___117_3721 = rc in
                                    let uu____3722 =
                                      let uu____3726 = star_type' env2 rt in
                                      Some uu____3726 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_3721.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____3722;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_3721.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  Some uu____3720)) in
                    let uu____3727 =
                      let comp1 =
                        let uu____3734 = is_monadic rc_opt1 in
                        let uu____3735 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3734 uu____3735 in
                      let uu____3736 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____3736,
                        (Some (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____3727 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____3769 =
                             let uu____3770 =
                               let uu____3780 =
                                 let uu____3782 =
                                   FStar_Syntax_Subst.closing_subst
                                     s_binders1 in
                                 subst_rc_opt uu____3782 s_rc_opt in
                               (s_binders1, s_body1, uu____3780) in
                             FStar_Syntax_Syntax.Tm_abs uu____3770 in
                           mk1 uu____3769 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____3790 =
                             let uu____3791 =
                               let uu____3801 =
                                 let uu____3803 =
                                   FStar_Syntax_Subst.closing_subst
                                     u_binders2 in
                                 subst_rc_opt uu____3803 u_rc_opt in
                               (u_binders2, u_body2, uu____3801) in
                             FStar_Syntax_Syntax.Tm_abs uu____3791 in
                           mk1 uu____3790 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.ty = uu____3811;
                FStar_Syntax_Syntax.p = uu____3812;_};
            FStar_Syntax_Syntax.fv_delta = uu____3813;
            FStar_Syntax_Syntax.fv_qual = uu____3814;_}
          ->
          let uu____3820 =
            let uu____3823 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____3823 in
          (match uu____3820 with
           | (uu____3839,t) ->
               let uu____3841 = let uu____3842 = normalize1 t in N uu____3842 in
               (uu____3841, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3859 = check_n env head1 in
          (match uu____3859 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3873 =
                   let uu____3874 = FStar_Syntax_Subst.compress t in
                   uu____3874.FStar_Syntax_Syntax.n in
                 match uu____3873 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3877 -> true
                 | uu____3885 -> false in
               let rec flatten1 t =
                 let uu____3897 =
                   let uu____3898 = FStar_Syntax_Subst.compress t in
                   uu____3898.FStar_Syntax_Syntax.n in
                 match uu____3897 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____3910);
                                FStar_Syntax_Syntax.tk = uu____3911;
                                FStar_Syntax_Syntax.pos = uu____3912;
                                FStar_Syntax_Syntax.vars = uu____3913;_})
                     when is_arrow t1 ->
                     let uu____3930 = flatten1 t1 in
                     (match uu____3930 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3982,uu____3983)
                     -> flatten1 e1
                 | uu____4012 ->
                     let uu____4013 =
                       let uu____4014 =
                         let uu____4015 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4015 in
                       FStar_Errors.Err uu____4014 in
                     raise uu____4013 in
               let uu____4023 = flatten1 t_head in
               (match uu____4023 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4075 =
                          let uu____4076 =
                            let uu____4077 = FStar_Util.string_of_int n1 in
                            let uu____4084 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4095 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4077 uu____4084 uu____4095 in
                          FStar_Errors.Err uu____4076 in
                        raise uu____4075)
                     else ();
                     (let uu____4103 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4103 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4130 args1 =
                            match uu____4130 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4173 =
                                       let uu____4174 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4174.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4173
                                 | (binders3,[]) ->
                                     let uu____4193 =
                                       let uu____4194 =
                                         let uu____4197 =
                                           let uu____4198 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4198 in
                                         FStar_Syntax_Subst.compress
                                           uu____4197 in
                                       uu____4194.FStar_Syntax_Syntax.n in
                                     (match uu____4193 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4214 =
                                            let uu____4215 =
                                              let uu____4216 =
                                                let uu____4224 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4224) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4216 in
                                            mk1 uu____4215 in
                                          N uu____4214
                                      | uu____4228 -> failwith "wat?")
                                 | ([],uu____4229::uu____4230) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4255)::binders3,(arg,uu____4258)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4292 = FStar_List.splitAt n' binders1 in
                          (match uu____4292 with
                           | (binders2,uu____4311) ->
                               let uu____4324 =
                                 let uu____4334 =
                                   FStar_List.map2
                                     (fun uu____4354  ->
                                        fun uu____4355  ->
                                          match (uu____4354, uu____4355) with
                                          | ((bv,uu____4372),(arg,q)) ->
                                              let uu____4379 =
                                                let uu____4380 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4380.FStar_Syntax_Syntax.n in
                                              (match uu____4379 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4390 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4403 ->
                                                   let uu____4404 =
                                                     check_n env arg in
                                                   (match uu____4404 with
                                                    | (uu____4415,s_arg,u_arg)
                                                        ->
                                                        let uu____4418 =
                                                          let uu____4422 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4422
                                                          then
                                                            let uu____4426 =
                                                              let uu____4429
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4429, q) in
                                                            [uu____4426;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4418))))
                                     binders2 args in
                                 FStar_List.split uu____4334 in
                               (match uu____4324 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4476 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4482 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4476, uu____4482)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4531) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4537) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4543,uu____4544) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4574 = let uu____4575 = env.tc_const c in N uu____4575 in
          (uu____4574, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4576 ->
          let uu____4584 =
            let uu____4585 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4585 in
          failwith uu____4584
      | FStar_Syntax_Syntax.Tm_type uu____4589 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4593 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4604 ->
          let uu____4609 =
            let uu____4610 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4610 in
          failwith uu____4609
      | FStar_Syntax_Syntax.Tm_uvar uu____4614 ->
          let uu____4623 =
            let uu____4624 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4624 in
          failwith uu____4623
      | FStar_Syntax_Syntax.Tm_delayed uu____4628 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4646 =
            let uu____4647 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4647 in
          failwith uu____4646
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
          let uu____4685 = check_n env e0 in
          match uu____4685 with
          | (uu____4692,s_e0,u_e0) ->
              let uu____4695 =
                let uu____4713 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4746 = FStar_Syntax_Subst.open_branch b in
                       match uu____4746 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___118_4778 = env in
                             let uu____4779 =
                               let uu____4780 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4780 in
                             {
                               env = uu____4779;
                               subst = (uu___118_4778.subst);
                               tc_const = (uu___118_4778.tc_const)
                             } in
                           let uu____4782 = f env1 body in
                           (match uu____4782 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4831 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4713 in
              (match uu____4695 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____4896 = FStar_List.hd nms in
                     match uu____4896 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___101_4900  ->
                          match uu___101_4900 with
                          | M uu____4901 -> true
                          | uu____4902 -> false) nms in
                   let uu____4903 =
                     let uu____4926 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____4978  ->
                              match uu____4978 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5101 =
                                         check env original_body (M t2) in
                                       (match uu____5101 with
                                        | (uu____5124,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5153,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____4926 in
                   (match uu____4903 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5272  ->
                                 match uu____5272 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5313 =
                                         let uu____5314 =
                                           let uu____5324 =
                                             let uu____5328 =
                                               let uu____5331 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5332 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5331, uu____5332) in
                                             [uu____5328] in
                                           (s_body, uu____5324) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5314 in
                                       mk1 uu____5313 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5354 =
                              let uu____5355 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5355] in
                            let uu____5356 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____5354 uu____5356
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____5361 =
                              let uu____5365 =
                                let uu____5366 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5366 in
                              [uu____5365] in
                            let uu____5367 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5361 uu____5367 in
                          let uu____5370 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5400 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5370, uu____5400)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5414 =
                             let uu____5417 =
                               let uu____5418 =
                                 let uu____5436 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5436,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5418 in
                             mk1 uu____5417 in
                           let uu____5463 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5414, uu____5463))))
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
              let uu____5506 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5506] in
            let uu____5507 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5507 with
            | (x_binders1,e21) ->
                let uu____5515 = infer env e1 in
                (match uu____5515 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5526 = is_C t1 in
                       if uu____5526
                       then
                         let uu___119_5527 = binding in
                         let uu____5528 =
                           let uu____5531 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5531 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_5527.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_5527.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5528;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_5527.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_5527.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_5534 = env in
                       let uu____5535 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_5536 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_5536.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_5536.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5535;
                         subst = (uu___120_5534.subst);
                         tc_const = (uu___120_5534.tc_const)
                       } in
                     let uu____5537 = proceed env1 e21 in
                     (match uu____5537 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_5548 = binding in
                            let uu____5549 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_5548.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_5548.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5549;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_5548.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_5548.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5552 =
                            let uu____5555 =
                              let uu____5556 =
                                let uu____5564 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_5569 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_5569.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_5569.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_5569.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_5569.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5564) in
                              FStar_Syntax_Syntax.Tm_let uu____5556 in
                            mk1 uu____5555 in
                          let uu____5570 =
                            let uu____5573 =
                              let uu____5574 =
                                let uu____5582 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_5587 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_5587.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_5587.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_5587.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_5587.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5582) in
                              FStar_Syntax_Syntax.Tm_let uu____5574 in
                            mk1 uu____5573 in
                          (nm_rec, uu____5552, uu____5570))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_5596 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_5596.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_5596.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_5596.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_5598 = env in
                       let uu____5599 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_5600 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_5600.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_5600.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5599;
                         subst = (uu___126_5598.subst);
                         tc_const = (uu___126_5598.tc_const)
                       } in
                     let uu____5601 = ensure_m env1 e21 in
                     (match uu____5601 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5618 =
                              let uu____5619 =
                                let uu____5629 =
                                  let uu____5633 =
                                    let uu____5636 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5637 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5636, uu____5637) in
                                  [uu____5633] in
                                (s_e2, uu____5629) in
                              FStar_Syntax_Syntax.Tm_app uu____5619 in
                            mk1 uu____5618 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____5649 =
                              let uu____5650 =
                                let uu____5660 =
                                  let uu____5664 =
                                    let uu____5667 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5667) in
                                  [uu____5664] in
                                (s_e1, uu____5660) in
                              FStar_Syntax_Syntax.Tm_app uu____5650 in
                            mk1 uu____5649 in
                          let uu____5675 =
                            let uu____5676 =
                              let uu____5677 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5677] in
                            FStar_Syntax_Util.abs uu____5676 body
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____5678 =
                            let uu____5681 =
                              let uu____5682 =
                                let uu____5690 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_5695 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_5695.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_5695.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_5695.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_5695.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5690) in
                              FStar_Syntax_Syntax.Tm_let uu____5682 in
                            mk1 uu____5681 in
                          ((M t2), uu____5675, uu____5678)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5704 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____5704 in
      let uu____5709 = check env e mn in
      match uu____5709 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5719 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5732 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____5732 in
      let uu____5737 = check env e mn in
      match uu____5737 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5747 -> failwith "[check_m]: impossible"
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
        (let uu____5769 =
           let uu____5770 = is_C c in Prims.op_Negation uu____5770 in
         if uu____5769 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____5782 =
           let uu____5783 = FStar_Syntax_Subst.compress c in
           uu____5783.FStar_Syntax_Syntax.n in
         match uu____5782 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5802 = FStar_Syntax_Util.head_and_args wp in
             (match uu____5802 with
              | (wp_head,wp_args) ->
                  ((let uu____5829 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5846 =
                           let uu____5847 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5847 in
                         Prims.op_Negation uu____5846) in
                    if uu____5829 then failwith "mismatch" else ());
                   (let uu____5859 =
                      let uu____5860 =
                        let uu____5870 =
                          FStar_List.map2
                            (fun uu____5880  ->
                               fun uu____5881  ->
                                 match (uu____5880, uu____5881) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____5904 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____5904
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____5907 = print_implicit q in
                                         let uu____5908 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____5907 uu____5908)
                                      else ();
                                      (let uu____5910 =
                                         trans_F_ env arg wp_arg in
                                       (uu____5910, q)))) args wp_args in
                        (head1, uu____5870) in
                      FStar_Syntax_Syntax.Tm_app uu____5860 in
                    mk1 uu____5859)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____5932 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____5932 with
              | (binders_orig,comp1) ->
                  let uu____5937 =
                    let uu____5945 =
                      FStar_List.map
                        (fun uu____5959  ->
                           match uu____5959 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____5972 = is_C h in
                               if uu____5972
                               then
                                 let w' =
                                   let uu____5979 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____5979 in
                                 let uu____5980 =
                                   let uu____5984 =
                                     let uu____5988 =
                                       let uu____5991 =
                                         let uu____5992 =
                                           let uu____5993 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____5993 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____5992 in
                                       (uu____5991, q) in
                                     [uu____5988] in
                                   (w', q) :: uu____5984 in
                                 (w', uu____5980)
                               else
                                 (let x =
                                    let uu____6005 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6005 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____5945 in
                  (match uu____5937 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6035 =
                           let uu____6037 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6037 in
                         FStar_Syntax_Subst.subst_comp uu____6035 comp1 in
                       let app =
                         let uu____6041 =
                           let uu____6042 =
                             let uu____6052 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6059 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6060 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6059, uu____6060)) bvs in
                             (wp, uu____6052) in
                           FStar_Syntax_Syntax.Tm_app uu____6042 in
                         mk1 uu____6041 in
                       let comp3 =
                         let uu____6065 = type_of_comp comp2 in
                         let uu____6066 = is_monadic_comp comp2 in
                         trans_G env uu____6065 uu____6066 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6068,uu____6069) ->
             trans_F_ env e wp
         | uu____6098 -> failwith "impossible trans_F_")
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
            let uu____6103 =
              let uu____6104 = star_type' env h in
              let uu____6107 =
                let uu____6113 =
                  let uu____6116 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6116) in
                [uu____6113] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6104;
                FStar_Syntax_Syntax.effect_args = uu____6107;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6103
          else
            (let uu____6122 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6122)
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
    fun t  -> let uu____6137 = n env.env t in star_type' env uu____6137
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6151 = n env.env t in check_n env uu____6151
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6164 = n env.env c in
        let uu____6165 = n env.env wp in trans_F_ env uu____6164 uu____6165