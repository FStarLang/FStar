open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ;}
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
              let uu___101_68 = a in
              let uu____69 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___101_68.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___101_68.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____69
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____77 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____77
             then
               (d "Elaborating extra WP combinators";
                (let uu____79 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____79))
             else ());
            (let rec collect_binders t =
               let uu____88 =
                 let uu____89 =
                   let uu____92 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____92 in
                 uu____89.FStar_Syntax_Syntax.n in
               match uu____88 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____114) -> t1
                     | uu____121 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____124 = collect_binders rest in
                   FStar_List.append bs uu____124
               | FStar_Syntax_Syntax.Tm_type uu____130 -> []
               | uu____133 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____145 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____145 FStar_Syntax_Util.name_binders in
             (let uu____156 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____156
              then
                let uu____157 =
                  let uu____158 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____158 in
                d uu____157
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____190 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____190 with
                | (sigelt,fv) ->
                    ((let uu____196 =
                        let uu____198 = FStar_ST.read sigelts in sigelt ::
                          uu____198 in
                      FStar_ST.write sigelts uu____196);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____219  ->
                     match uu____219 with
                     | (t,b) ->
                         let uu____226 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____226)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____243 = FStar_Syntax_Syntax.as_implicit true in
                     ((fst t), uu____243)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____256 = FStar_Syntax_Syntax.bv_to_name (fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____256) in
              let uu____257 =
                let uu____269 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let body =
                      let uu____289 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____289 in
                    let uu____292 =
                      let uu____293 =
                        let uu____297 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____298 =
                          let uu____300 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____300] in
                        uu____297 :: uu____298 in
                      FStar_List.append binders uu____293 in
                    FStar_Syntax_Util.abs uu____292 body None in
                  let uu____308 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____309 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____308, uu____309) in
                match uu____269 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____340 =
                        let uu____341 =
                          let uu____351 =
                            let uu____355 =
                              FStar_List.map
                                (fun uu____363  ->
                                   match uu____363 with
                                   | (bv,uu____369) ->
                                       let uu____370 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____371 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____370, uu____371)) binders in
                            let uu____372 =
                              let uu____376 =
                                let uu____379 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____380 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____379, uu____380) in
                              let uu____381 =
                                let uu____385 =
                                  let uu____388 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____388) in
                                [uu____385] in
                              uu____376 :: uu____381 in
                            FStar_List.append uu____355 uu____372 in
                          (fv, uu____351) in
                        FStar_Syntax_Syntax.Tm_app uu____341 in
                      mk1 uu____340 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____257 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____434 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____434 in
                    let ret1 =
                      let uu____442 =
                        let uu____448 =
                          let uu____449 =
                            let uu____452 =
                              let uu____453 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____453 in
                            FStar_Syntax_Syntax.mk_Total uu____452 in
                          FStar_Syntax_Util.lcomp_of_comp uu____449 in
                        FStar_Util.Inl uu____448 in
                      Some uu____442 in
                    let body =
                      let uu____463 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____463 ret1 in
                    let uu____464 =
                      let uu____465 = mk_all_implicit binders in
                      let uu____469 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____465 uu____469 in
                    FStar_Syntax_Util.abs uu____464 body ret1 in
                  let c_pure1 =
                    let uu____484 = mk_lid "pure" in
                    register env1 uu____484 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____489 =
                        let uu____490 =
                          let uu____491 =
                            let uu____495 =
                              let uu____496 =
                                let uu____497 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____497 in
                              FStar_Syntax_Syntax.mk_binder uu____496 in
                            [uu____495] in
                          let uu____498 =
                            let uu____501 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____501 in
                          FStar_Syntax_Util.arrow uu____491 uu____498 in
                        mk_gctx uu____490 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____489 in
                    let r =
                      let uu____503 =
                        let uu____504 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____504 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____503 in
                    let ret1 =
                      let uu____512 =
                        let uu____518 =
                          let uu____519 =
                            let uu____522 =
                              let uu____523 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____523 in
                            FStar_Syntax_Syntax.mk_Total uu____522 in
                          FStar_Syntax_Util.lcomp_of_comp uu____519 in
                        FStar_Util.Inl uu____518 in
                      Some uu____512 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____538 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____541 =
                          let uu____547 =
                            let uu____549 =
                              let uu____550 =
                                let uu____551 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____551
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____550 in
                            [uu____549] in
                          FStar_List.append gamma_as_args uu____547 in
                        FStar_Syntax_Util.mk_app uu____538 uu____541 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____554 =
                      let uu____555 = mk_all_implicit binders in
                      let uu____559 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____555 uu____559 in
                    FStar_Syntax_Util.abs uu____554 outer_body ret1 in
                  let c_app1 =
                    let uu____578 = mk_lid "app" in
                    register env1 uu____578 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____585 =
                        let uu____589 =
                          let uu____590 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____590 in
                        [uu____589] in
                      let uu____591 =
                        let uu____594 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____594 in
                      FStar_Syntax_Util.arrow uu____585 uu____591 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____597 =
                        let uu____598 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____598 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____597 in
                    let ret1 =
                      let uu____606 =
                        let uu____612 =
                          let uu____613 =
                            let uu____616 =
                              let uu____617 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____617 in
                            FStar_Syntax_Syntax.mk_Total uu____616 in
                          FStar_Syntax_Util.lcomp_of_comp uu____613 in
                        FStar_Util.Inl uu____612 in
                      Some uu____606 in
                    let uu____626 =
                      let uu____627 = mk_all_implicit binders in
                      let uu____631 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____627 uu____631 in
                    let uu____649 =
                      let uu____650 =
                        let uu____656 =
                          let uu____658 =
                            let uu____661 =
                              let uu____667 =
                                let uu____669 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____669] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____667 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____661 in
                          let uu____670 =
                            let uu____674 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____674] in
                          uu____658 :: uu____670 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____656 in
                      FStar_Syntax_Util.mk_app c_app1 uu____650 in
                    FStar_Syntax_Util.abs uu____626 uu____649 ret1 in
                  let c_lift11 =
                    let uu____678 = mk_lid "lift1" in
                    register env1 uu____678 c_lift1 in
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
                      let uu____686 =
                        let uu____690 =
                          let uu____691 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____691 in
                        let uu____692 =
                          let uu____694 =
                            let uu____695 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____695 in
                          [uu____694] in
                        uu____690 :: uu____692 in
                      let uu____696 =
                        let uu____699 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____699 in
                      FStar_Syntax_Util.arrow uu____686 uu____696 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____702 =
                        let uu____703 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____703 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____702 in
                    let a2 =
                      let uu____705 =
                        let uu____706 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____706 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____705 in
                    let ret1 =
                      let uu____714 =
                        let uu____720 =
                          let uu____721 =
                            let uu____724 =
                              let uu____725 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____725 in
                            FStar_Syntax_Syntax.mk_Total uu____724 in
                          FStar_Syntax_Util.lcomp_of_comp uu____721 in
                        FStar_Util.Inl uu____720 in
                      Some uu____714 in
                    let uu____734 =
                      let uu____735 = mk_all_implicit binders in
                      let uu____739 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____735 uu____739 in
                    let uu____761 =
                      let uu____762 =
                        let uu____768 =
                          let uu____770 =
                            let uu____773 =
                              let uu____779 =
                                let uu____781 =
                                  let uu____784 =
                                    let uu____790 =
                                      let uu____792 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____792] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____790 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____784 in
                                let uu____793 =
                                  let uu____797 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____797] in
                                uu____781 :: uu____793 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____779 in
                            FStar_Syntax_Util.mk_app c_app1 uu____773 in
                          let uu____800 =
                            let uu____804 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____804] in
                          uu____770 :: uu____800 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____768 in
                      FStar_Syntax_Util.mk_app c_app1 uu____762 in
                    FStar_Syntax_Util.abs uu____734 uu____761 ret1 in
                  let c_lift21 =
                    let uu____808 = mk_lid "lift2" in
                    register env1 uu____808 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____815 =
                        let uu____819 =
                          let uu____820 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____820 in
                        [uu____819] in
                      let uu____821 =
                        let uu____824 =
                          let uu____825 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____825 in
                        FStar_Syntax_Syntax.mk_Total uu____824 in
                      FStar_Syntax_Util.arrow uu____815 uu____821 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____834 =
                        let uu____840 =
                          let uu____841 =
                            let uu____844 =
                              let uu____845 =
                                let uu____846 =
                                  let uu____850 =
                                    let uu____851 =
                                      FStar_Syntax_Syntax.bv_to_name t1 in
                                    FStar_Syntax_Syntax.null_binder uu____851 in
                                  [uu____850] in
                                let uu____852 =
                                  let uu____855 =
                                    FStar_Syntax_Syntax.bv_to_name t2 in
                                  FStar_Syntax_Syntax.mk_GTotal uu____855 in
                                FStar_Syntax_Util.arrow uu____846 uu____852 in
                              mk_ctx uu____845 in
                            FStar_Syntax_Syntax.mk_Total uu____844 in
                          FStar_Syntax_Util.lcomp_of_comp uu____841 in
                        FStar_Util.Inl uu____840 in
                      Some uu____834 in
                    let e1 =
                      let uu____865 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____865 in
                    let body =
                      let uu____867 =
                        let uu____868 =
                          let uu____872 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____872] in
                        FStar_List.append gamma uu____868 in
                      let uu____875 =
                        let uu____876 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____879 =
                          let uu____885 =
                            let uu____886 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____886 in
                          let uu____887 = args_of_binders1 gamma in uu____885
                            :: uu____887 in
                        FStar_Syntax_Util.mk_app uu____876 uu____879 in
                      FStar_Syntax_Util.abs uu____867 uu____875 ret1 in
                    let uu____889 =
                      let uu____890 = mk_all_implicit binders in
                      let uu____894 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____890 uu____894 in
                    FStar_Syntax_Util.abs uu____889 body ret1 in
                  let c_push1 =
                    let uu____911 = mk_lid "push" in
                    register env1 uu____911 c_push in
                  let ret_tot_wp_a =
                    let uu____919 =
                      let uu____925 =
                        let uu____926 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____926 in
                      FStar_Util.Inl uu____925 in
                    Some uu____919 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____957 =
                        let uu____958 =
                          let uu____968 = args_of_binders1 binders in
                          (c, uu____968) in
                        FStar_Syntax_Syntax.Tm_app uu____958 in
                      mk1 uu____957
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____976 =
                        let uu____977 =
                          let uu____981 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____982 =
                            let uu____984 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____984] in
                          uu____981 :: uu____982 in
                        let uu____985 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____977 uu____985 in
                      FStar_Syntax_Syntax.mk_Total uu____976 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____989 =
                      let uu____990 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____990 in
                    let uu____996 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____998 =
                        let uu____1001 =
                          let uu____1007 =
                            let uu____1009 =
                              let uu____1012 =
                                let uu____1018 =
                                  let uu____1019 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1019 in
                                [uu____1018] in
                              FStar_Syntax_Util.mk_app l_ite uu____1012 in
                            [uu____1009] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1007 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1001 in
                      FStar_Syntax_Util.ascribe uu____998
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____989 uu____996
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1044 = mk_lid "wp_if_then_else" in
                    register env1 uu____1044 wp_if_then_else in
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
                      let uu____1055 =
                        let uu____1061 =
                          let uu____1063 =
                            let uu____1066 =
                              let uu____1072 =
                                let uu____1074 =
                                  let uu____1077 =
                                    let uu____1083 =
                                      let uu____1084 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1084 in
                                    [uu____1083] in
                                  FStar_Syntax_Util.mk_app l_and uu____1077 in
                                [uu____1074] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1072 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1066 in
                          let uu____1089 =
                            let uu____1093 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1093] in
                          uu____1063 :: uu____1089 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1061 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1055 in
                    let uu____1096 =
                      let uu____1097 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1097 in
                    FStar_Syntax_Util.abs uu____1096 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1104 = mk_lid "wp_assert" in
                    register env1 uu____1104 wp_assert in
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
                      let uu____1115 =
                        let uu____1121 =
                          let uu____1123 =
                            let uu____1126 =
                              let uu____1132 =
                                let uu____1134 =
                                  let uu____1137 =
                                    let uu____1143 =
                                      let uu____1144 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1144 in
                                    [uu____1143] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1137 in
                                [uu____1134] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1132 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1126 in
                          let uu____1149 =
                            let uu____1153 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1153] in
                          uu____1123 :: uu____1149 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1121 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1115 in
                    let uu____1156 =
                      let uu____1157 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1157 in
                    FStar_Syntax_Util.abs uu____1156 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1164 = mk_lid "wp_assume" in
                    register env1 uu____1164 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1173 =
                        let uu____1177 =
                          let uu____1178 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1178 in
                        [uu____1177] in
                      let uu____1179 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1173 uu____1179 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1186 =
                        let uu____1192 =
                          let uu____1194 =
                            let uu____1197 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1197 in
                          let uu____1203 =
                            let uu____1207 =
                              let uu____1210 =
                                let uu____1216 =
                                  let uu____1218 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1218] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1216 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1210 in
                            [uu____1207] in
                          uu____1194 :: uu____1203 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1192 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1186 in
                    let uu____1225 =
                      let uu____1226 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1226 in
                    FStar_Syntax_Util.abs uu____1225 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1233 = mk_lid "wp_close" in
                    register env1 uu____1233 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1244 =
                      let uu____1250 =
                        let uu____1251 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1251 in
                      FStar_Util.Inl uu____1250 in
                    Some uu____1244 in
                  let ret_gtot_type =
                    let uu____1271 =
                      let uu____1277 =
                        let uu____1278 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1278 in
                      FStar_Util.Inl uu____1277 in
                    Some uu____1271 in
                  let mk_forall1 x body =
                    let uu____1298 =
                      let uu____1301 =
                        let uu____1302 =
                          let uu____1312 =
                            let uu____1314 =
                              let uu____1315 =
                                let uu____1316 =
                                  let uu____1317 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1317] in
                                FStar_Syntax_Util.abs uu____1316 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1315 in
                            [uu____1314] in
                          (FStar_Syntax_Util.tforall, uu____1312) in
                        FStar_Syntax_Syntax.Tm_app uu____1302 in
                      FStar_Syntax_Syntax.mk uu____1301 in
                    uu____1298 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1331 =
                      let uu____1332 = FStar_Syntax_Subst.compress t in
                      uu____1332.FStar_Syntax_Syntax.n in
                    match uu____1331 with
                    | FStar_Syntax_Syntax.Tm_type uu____1335 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1350  ->
                              match uu____1350 with
                              | (b,uu____1354) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1355 -> true in
                  let rec is_monotonic t =
                    let uu____1360 =
                      let uu____1361 = FStar_Syntax_Subst.compress t in
                      uu____1361.FStar_Syntax_Syntax.n in
                    match uu____1360 with
                    | FStar_Syntax_Syntax.Tm_type uu____1364 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1379  ->
                              match uu____1379 with
                              | (b,uu____1383) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1384 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1436 =
                      let uu____1437 = FStar_Syntax_Subst.compress t1 in
                      uu____1437.FStar_Syntax_Syntax.n in
                    match uu____1436 with
                    | FStar_Syntax_Syntax.Tm_type uu____1440 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1443);
                                      FStar_Syntax_Syntax.tk = uu____1444;
                                      FStar_Syntax_Syntax.pos = uu____1445;
                                      FStar_Syntax_Syntax.vars = uu____1446;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1469 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1469
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1472 =
                              let uu____1475 =
                                let uu____1481 =
                                  let uu____1482 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1482 in
                                [uu____1481] in
                              FStar_Syntax_Util.mk_app x uu____1475 in
                            let uu____1483 =
                              let uu____1486 =
                                let uu____1492 =
                                  let uu____1493 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1493 in
                                [uu____1492] in
                              FStar_Syntax_Util.mk_app y uu____1486 in
                            mk_rel1 b uu____1472 uu____1483 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1498 =
                               let uu____1499 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1502 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1499 uu____1502 in
                             let uu____1505 =
                               let uu____1506 =
                                 let uu____1509 =
                                   let uu____1515 =
                                     let uu____1516 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1516 in
                                   [uu____1515] in
                                 FStar_Syntax_Util.mk_app x uu____1509 in
                               let uu____1517 =
                                 let uu____1520 =
                                   let uu____1526 =
                                     let uu____1527 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1527 in
                                   [uu____1526] in
                                 FStar_Syntax_Util.mk_app y uu____1520 in
                               mk_rel1 b uu____1506 uu____1517 in
                             FStar_Syntax_Util.mk_imp uu____1498 uu____1505 in
                           let uu____1528 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1528)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1531);
                                      FStar_Syntax_Syntax.tk = uu____1532;
                                      FStar_Syntax_Syntax.pos = uu____1533;
                                      FStar_Syntax_Syntax.vars = uu____1534;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1557 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1557
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1560 =
                              let uu____1563 =
                                let uu____1569 =
                                  let uu____1570 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1570 in
                                [uu____1569] in
                              FStar_Syntax_Util.mk_app x uu____1563 in
                            let uu____1571 =
                              let uu____1574 =
                                let uu____1580 =
                                  let uu____1581 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1581 in
                                [uu____1580] in
                              FStar_Syntax_Util.mk_app y uu____1574 in
                            mk_rel1 b uu____1560 uu____1571 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1586 =
                               let uu____1587 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1590 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1587 uu____1590 in
                             let uu____1593 =
                               let uu____1594 =
                                 let uu____1597 =
                                   let uu____1603 =
                                     let uu____1604 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1604 in
                                   [uu____1603] in
                                 FStar_Syntax_Util.mk_app x uu____1597 in
                               let uu____1605 =
                                 let uu____1608 =
                                   let uu____1614 =
                                     let uu____1615 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1615 in
                                   [uu____1614] in
                                 FStar_Syntax_Util.mk_app y uu____1608 in
                               mk_rel1 b uu____1594 uu____1605 in
                             FStar_Syntax_Util.mk_imp uu____1586 uu____1593 in
                           let uu____1616 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1616)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___102_1637 = t1 in
                          let uu____1638 =
                            let uu____1639 =
                              let uu____1647 =
                                let uu____1648 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1648 in
                              ([binder], uu____1647) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1639 in
                          {
                            FStar_Syntax_Syntax.n = uu____1638;
                            FStar_Syntax_Syntax.tk =
                              (uu___102_1637.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___102_1637.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___102_1637.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1660 ->
                        failwith "unhandled arrow"
                    | uu____1668 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1683 =
                        let uu____1684 = FStar_Syntax_Subst.compress t1 in
                        uu____1684.FStar_Syntax_Syntax.n in
                      match uu____1683 with
                      | FStar_Syntax_Syntax.Tm_type uu____1687 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1704 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1704
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1719 =
                                let uu____1720 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1720 i in
                              FStar_Syntax_Syntax.fvar uu____1719
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1744 =
                            let uu____1748 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1753  ->
                                     match uu____1753 with
                                     | (t2,q) ->
                                         let uu____1758 = project i x in
                                         let uu____1759 = project i y in
                                         mk_stronger t2 uu____1758 uu____1759)
                                args in
                            match uu____1748 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1744 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1776);
                                      FStar_Syntax_Syntax.tk = uu____1777;
                                      FStar_Syntax_Syntax.pos = uu____1778;
                                      FStar_Syntax_Syntax.vars = uu____1779;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1801  ->
                                   match uu____1801 with
                                   | (bv,q) ->
                                       let uu____1806 =
                                         let uu____1807 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1807 in
                                       FStar_Syntax_Syntax.gen_bv uu____1806
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1811 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1811) bvs in
                          let body =
                            let uu____1813 = FStar_Syntax_Util.mk_app x args in
                            let uu____1814 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1813 uu____1814 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1819);
                                      FStar_Syntax_Syntax.tk = uu____1820;
                                      FStar_Syntax_Syntax.pos = uu____1821;
                                      FStar_Syntax_Syntax.vars = uu____1822;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1844  ->
                                   match uu____1844 with
                                   | (bv,q) ->
                                       let uu____1849 =
                                         let uu____1850 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1850 in
                                       FStar_Syntax_Syntax.gen_bv uu____1849
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1854 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1854) bvs in
                          let body =
                            let uu____1856 = FStar_Syntax_Util.mk_app x args in
                            let uu____1857 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1856 uu____1857 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1860 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1862 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1863 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1864 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1862 uu____1863 uu____1864 in
                    let uu____1865 =
                      let uu____1866 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1866 in
                    FStar_Syntax_Util.abs uu____1865 body ret_tot_type in
                  let stronger1 =
                    let uu____1881 = mk_lid "stronger" in
                    register env1 uu____1881 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1887 = FStar_Util.prefix gamma in
                    match uu____1887 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1913 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1913 in
                          let uu____1916 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1916 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1924 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1924 in
                              let guard_free1 =
                                let uu____1931 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1931 in
                              let pat =
                                let uu____1935 =
                                  let uu____1941 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1941] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1935 in
                              let pattern_guarded_body =
                                let uu____1945 =
                                  let uu____1946 =
                                    let uu____1951 =
                                      let uu____1952 =
                                        let uu____1959 =
                                          let uu____1961 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1961] in
                                        [uu____1959] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1952 in
                                    (body, uu____1951) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1946 in
                                mk1 uu____1945 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1964 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1967 =
                            let uu____1968 =
                              let uu____1969 =
                                let uu____1970 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1973 =
                                  let uu____1979 = args_of_binders1 wp_args in
                                  let uu____1981 =
                                    let uu____1983 =
                                      let uu____1984 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1984 in
                                    [uu____1983] in
                                  FStar_List.append uu____1979 uu____1981 in
                                FStar_Syntax_Util.mk_app uu____1970
                                  uu____1973 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1969 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1968 in
                          FStar_Syntax_Util.abs gamma uu____1967
                            ret_gtot_type in
                        let uu____1985 =
                          let uu____1986 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1986 in
                        FStar_Syntax_Util.abs uu____1985 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1993 = mk_lid "wp_ite" in
                    register env1 uu____1993 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1999 = FStar_Util.prefix gamma in
                    match uu____1999 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2023 =
                            let uu____2024 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2027 =
                              let uu____2033 =
                                let uu____2034 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2034 in
                              [uu____2033] in
                            FStar_Syntax_Util.mk_app uu____2024 uu____2027 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2023 in
                        let uu____2035 =
                          let uu____2036 =
                            let uu____2040 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2040 gamma in
                          FStar_List.append binders uu____2036 in
                        FStar_Syntax_Util.abs uu____2035 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2049 = mk_lid "null_wp" in
                    register env1 uu____2049 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2058 =
                        let uu____2064 =
                          let uu____2066 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2067 =
                            let uu____2069 =
                              let uu____2072 =
                                let uu____2078 =
                                  let uu____2079 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2079 in
                                [uu____2078] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2072 in
                            let uu____2080 =
                              let uu____2084 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2084] in
                            uu____2069 :: uu____2080 in
                          uu____2066 :: uu____2067 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2064 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2058 in
                    let uu____2087 =
                      let uu____2088 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2088 in
                    FStar_Syntax_Util.abs uu____2087 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2095 = mk_lid "wp_trivial" in
                    register env1 uu____2095 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2100 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2100
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2105 =
                      let uu____2107 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2107 in
                    let uu____2112 =
                      let uu___103_2113 = ed in
                      let uu____2114 =
                        let uu____2115 = c wp_if_then_else2 in
                        ([], uu____2115) in
                      let uu____2117 =
                        let uu____2118 = c wp_ite2 in ([], uu____2118) in
                      let uu____2120 =
                        let uu____2121 = c stronger2 in ([], uu____2121) in
                      let uu____2123 =
                        let uu____2124 = c wp_close2 in ([], uu____2124) in
                      let uu____2126 =
                        let uu____2127 = c wp_assert2 in ([], uu____2127) in
                      let uu____2129 =
                        let uu____2130 = c wp_assume2 in ([], uu____2130) in
                      let uu____2132 =
                        let uu____2133 = c null_wp2 in ([], uu____2133) in
                      let uu____2135 =
                        let uu____2136 = c wp_trivial2 in ([], uu____2136) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_2113.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_2113.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_2113.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_2113.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_2113.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_2113.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_2113.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2114;
                        FStar_Syntax_Syntax.ite_wp = uu____2117;
                        FStar_Syntax_Syntax.stronger = uu____2120;
                        FStar_Syntax_Syntax.close_wp = uu____2123;
                        FStar_Syntax_Syntax.assert_p = uu____2126;
                        FStar_Syntax_Syntax.assume_p = uu____2129;
                        FStar_Syntax_Syntax.null_wp = uu____2132;
                        FStar_Syntax_Syntax.trivial = uu____2135;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_2113.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_2113.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_2113.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_2113.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2105, uu____2112)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_2148 = dmff_env in
      {
        env = env';
        subst = (uu___104_2148.subst);
        tc_const = (uu___104_2148.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2161 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2173 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___90_2183  ->
    match uu___90_2183 with
    | FStar_Syntax_Syntax.Total (t,uu____2185) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___89_2194  ->
                match uu___89_2194 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2195 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2197 =
          let uu____2198 =
            let uu____2199 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2199 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2198 in
        failwith uu____2197
    | FStar_Syntax_Syntax.GTotal uu____2200 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___91_2208  ->
    match uu___91_2208 with
    | N t ->
        let uu____2210 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2210
    | M t ->
        let uu____2212 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2212
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2216,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2218;
                      FStar_Syntax_Syntax.pos = uu____2219;
                      FStar_Syntax_Syntax.vars = uu____2220;_})
        -> nm_of_comp n2
    | uu____2231 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2243 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2243 with | M uu____2244 -> true | N uu____2245 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2249 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2259 =
        let uu____2263 =
          let uu____2264 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2264 in
        [uu____2263] in
      let uu____2265 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2259 uu____2265 in
    let uu____2268 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2268
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
          (let uu____2303 =
             let uu____2311 =
               let uu____2315 =
                 let uu____2318 =
                   let uu____2319 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2319 in
                 let uu____2320 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2318, uu____2320) in
               [uu____2315] in
             let uu____2325 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2311, uu____2325) in
           FStar_Syntax_Syntax.Tm_arrow uu____2303)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2354) ->
          let binders1 =
            FStar_List.map
              (fun uu____2373  ->
                 match uu____2373 with
                 | (bv,aqual) ->
                     let uu____2380 =
                       let uu___105_2381 = bv in
                       let uu____2382 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_2381.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_2381.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2382
                       } in
                     (uu____2380, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2385,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2387);
                             FStar_Syntax_Syntax.tk = uu____2388;
                             FStar_Syntax_Syntax.pos = uu____2389;
                             FStar_Syntax_Syntax.vars = uu____2390;_})
               ->
               let uu____2407 =
                 let uu____2408 =
                   let uu____2416 =
                     let uu____2417 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2417 in
                   (binders1, uu____2416) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2408 in
               mk1 uu____2407
           | uu____2421 ->
               let uu____2422 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2422 with
                | N hn ->
                    let uu____2424 =
                      let uu____2425 =
                        let uu____2433 =
                          let uu____2434 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2434 in
                        (binders1, uu____2433) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2425 in
                    mk1 uu____2424
                | M a ->
                    let uu____2439 =
                      let uu____2440 =
                        let uu____2448 =
                          let uu____2452 =
                            let uu____2456 =
                              let uu____2459 =
                                let uu____2460 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2460 in
                              let uu____2461 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2459, uu____2461) in
                            [uu____2456] in
                          FStar_List.append binders1 uu____2452 in
                        let uu____2468 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2448, uu____2468) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2440 in
                    mk1 uu____2439))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2519 = f x in
                    FStar_Util.string_builder_append strb uu____2519);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2523 = f x1 in
                         FStar_Util.string_builder_append strb uu____2523))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2525 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2526 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2525 uu____2526 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2534 =
              let uu____2535 = FStar_Syntax_Subst.compress ty in
              uu____2535.FStar_Syntax_Syntax.n in
            match uu____2534 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2550 =
                  let uu____2551 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2551 in
                if uu____2550
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2565 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2565 s in
                       let uu____2567 =
                         let uu____2568 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2568 in
                       if uu____2567
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2571 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2571 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2582  ->
                                  match uu____2582 with
                                  | (bv,uu____2588) ->
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
            | uu____2603 ->
                ((let uu____2605 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2605);
                 false) in
          let rec is_valid_application head2 =
            let uu____2610 =
              let uu____2611 = FStar_Syntax_Subst.compress head2 in
              uu____2611.FStar_Syntax_Syntax.n in
            match uu____2610 with
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
                  (let uu____2615 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2615)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2630 -> true
                 | uu____2640 ->
                     ((let uu____2642 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2642);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2643 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2644 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2646) ->
                is_valid_application t2
            | uu____2651 -> false in
          let uu____2652 = is_valid_application head1 in
          if uu____2652
          then
            let uu____2653 =
              let uu____2654 =
                let uu____2664 =
                  FStar_List.map
                    (fun uu____2674  ->
                       match uu____2674 with
                       | (t2,qual) ->
                           let uu____2687 = star_type' env t2 in
                           (uu____2687, qual)) args in
                (head1, uu____2664) in
              FStar_Syntax_Syntax.Tm_app uu____2654 in
            mk1 uu____2653
          else
            (let uu____2694 =
               let uu____2695 =
                 let uu____2696 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2696 in
               FStar_Errors.Err uu____2695 in
             raise uu____2694)
      | FStar_Syntax_Syntax.Tm_bvar uu____2697 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2698 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2699 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2700 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2726 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2726 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___108_2732 = env in
                 let uu____2733 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2733;
                   subst = (uu___108_2732.subst);
                   tc_const = (uu___108_2732.tc_const)
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
               ((let uu___109_2750 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_2750.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_2750.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2757 =
            let uu____2758 =
              let uu____2763 = star_type' env t2 in (uu____2763, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2758 in
          mk1 uu____2757
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2801 =
            let uu____2802 =
              let uu____2820 = star_type' env e in
              let uu____2821 =
                let uu____2831 =
                  let uu____2836 = star_type' env t2 in
                  FStar_Util.Inl uu____2836 in
                (uu____2831, None) in
              (uu____2820, uu____2821, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2802 in
          mk1 uu____2801
      | FStar_Syntax_Syntax.Tm_ascribed uu____2858 ->
          let uu____2876 =
            let uu____2877 =
              let uu____2878 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2878 in
            FStar_Errors.Err uu____2877 in
          raise uu____2876
      | FStar_Syntax_Syntax.Tm_refine uu____2879 ->
          let uu____2884 =
            let uu____2885 =
              let uu____2886 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2886 in
            FStar_Errors.Err uu____2885 in
          raise uu____2884
      | FStar_Syntax_Syntax.Tm_uinst uu____2887 ->
          let uu____2892 =
            let uu____2893 =
              let uu____2894 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2894 in
            FStar_Errors.Err uu____2893 in
          raise uu____2892
      | FStar_Syntax_Syntax.Tm_constant uu____2895 ->
          let uu____2896 =
            let uu____2897 =
              let uu____2898 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2898 in
            FStar_Errors.Err uu____2897 in
          raise uu____2896
      | FStar_Syntax_Syntax.Tm_match uu____2899 ->
          let uu____2915 =
            let uu____2916 =
              let uu____2917 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2917 in
            FStar_Errors.Err uu____2916 in
          raise uu____2915
      | FStar_Syntax_Syntax.Tm_let uu____2918 ->
          let uu____2926 =
            let uu____2927 =
              let uu____2928 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2928 in
            FStar_Errors.Err uu____2927 in
          raise uu____2926
      | FStar_Syntax_Syntax.Tm_uvar uu____2929 ->
          let uu____2938 =
            let uu____2939 =
              let uu____2940 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2940 in
            FStar_Errors.Err uu____2939 in
          raise uu____2938
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2941 =
            let uu____2942 =
              let uu____2943 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2943 in
            FStar_Errors.Err uu____2942 in
          raise uu____2941
      | FStar_Syntax_Syntax.Tm_delayed uu____2944 -> failwith "impossible"
let is_monadic uu___93_2977 =
  match uu___93_2977 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____2989;
        FStar_Syntax_Syntax.res_typ = uu____2990;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____2992;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3009  ->
              match uu___92_3009 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3010 -> false))
  | Some (FStar_Util.Inr (uu____3011,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3024  ->
              match uu___92_3024 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3025 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3029 =
      let uu____3030 = FStar_Syntax_Subst.compress t in
      uu____3030.FStar_Syntax_Syntax.n in
    match uu____3029 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3050 =
            let uu____3051 = FStar_List.hd args in fst uu____3051 in
          is_C uu____3050 in
        if r
        then
          ((let uu____3063 =
              let uu____3064 =
                FStar_List.for_all
                  (fun uu____3067  ->
                     match uu____3067 with | (h,uu____3071) -> is_C h) args in
              Prims.op_Negation uu____3064 in
            if uu____3063 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3075 =
              let uu____3076 =
                FStar_List.for_all
                  (fun uu____3079  ->
                     match uu____3079 with
                     | (h,uu____3083) ->
                         let uu____3084 = is_C h in
                         Prims.op_Negation uu____3084) args in
              Prims.op_Negation uu____3076 in
            if uu____3075 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3098 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3098 with
         | M t1 ->
             ((let uu____3101 = is_C t1 in
               if uu____3101 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3105) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3111) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3117,uu____3118) -> is_C t1
    | uu____3147 -> false
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
          let uu____3174 =
            let uu____3175 =
              let uu____3185 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3186 =
                let uu____3190 =
                  let uu____3193 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3193) in
                [uu____3190] in
              (uu____3185, uu____3186) in
            FStar_Syntax_Syntax.Tm_app uu____3175 in
          mk1 uu____3174 in
        let uu____3201 =
          let uu____3202 = FStar_Syntax_Syntax.mk_binder p in [uu____3202] in
        let uu____3203 =
          let uu____3210 =
            let uu____3216 =
              let uu____3217 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3217 in
            FStar_Util.Inl uu____3216 in
          Some uu____3210 in
        FStar_Syntax_Util.abs uu____3201 body uu____3203
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___94_3230  ->
    match uu___94_3230 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3231 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3365 =
          match uu____3365 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3386 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3387 =
                       let uu____3388 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3388 in
                     Prims.op_Negation uu____3387) in
                if uu____3386
                then
                  let uu____3389 =
                    let uu____3390 =
                      let uu____3391 = FStar_Syntax_Print.term_to_string e in
                      let uu____3392 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3393 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3391 uu____3392 uu____3393 in
                    FStar_Errors.Err uu____3390 in
                  raise uu____3389
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3407 = mk_return env t1 s_e in
                     ((M t1), uu____3407, u_e)))
               | (M t1,N t2) ->
                   let uu____3410 =
                     let uu____3411 =
                       let uu____3412 = FStar_Syntax_Print.term_to_string e in
                       let uu____3413 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3414 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3412 uu____3413 uu____3414 in
                     FStar_Errors.Err uu____3411 in
                   raise uu____3410) in
        let ensure_m env1 e2 =
          let strip_m uu___95_3440 =
            match uu___95_3440 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3450 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3461 =
                let uu____3462 =
                  let uu____3465 =
                    let uu____3466 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3466 in
                  (uu____3465, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3462 in
              raise uu____3461
          | M uu____3470 ->
              let uu____3471 = check env1 e2 context_nm in strip_m uu____3471 in
        let uu____3475 =
          let uu____3476 = FStar_Syntax_Subst.compress e in
          uu____3476.FStar_Syntax_Syntax.n in
        match uu____3475 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3482 ->
            let uu____3483 = infer env e in return_if uu____3483
        | FStar_Syntax_Syntax.Tm_name uu____3487 ->
            let uu____3488 = infer env e in return_if uu____3488
        | FStar_Syntax_Syntax.Tm_fvar uu____3492 ->
            let uu____3493 = infer env e in return_if uu____3493
        | FStar_Syntax_Syntax.Tm_abs uu____3497 ->
            let uu____3512 = infer env e in return_if uu____3512
        | FStar_Syntax_Syntax.Tm_constant uu____3516 ->
            let uu____3517 = infer env e in return_if uu____3517
        | FStar_Syntax_Syntax.Tm_app uu____3521 ->
            let uu____3531 = infer env e in return_if uu____3531
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3578) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3584) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3590,uu____3591) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3620 ->
            let uu____3628 =
              let uu____3629 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3629 in
            failwith uu____3628
        | FStar_Syntax_Syntax.Tm_type uu____3633 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3637 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3648 ->
            let uu____3653 =
              let uu____3654 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3654 in
            failwith uu____3653
        | FStar_Syntax_Syntax.Tm_uvar uu____3658 ->
            let uu____3667 =
              let uu____3668 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3668 in
            failwith uu____3667
        | FStar_Syntax_Syntax.Tm_delayed uu____3672 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3696 =
              let uu____3697 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3697 in
            failwith uu____3696
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
      let uu____3719 =
        let uu____3720 = FStar_Syntax_Subst.compress e in
        uu____3720.FStar_Syntax_Syntax.n in
      match uu____3719 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___110_3760 = env in
            let uu____3761 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3761;
              subst = (uu___110_3760.subst);
              tc_const = (uu___110_3760.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3770  ->
                 match uu____3770 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___111_3778 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___111_3778.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___111_3778.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3779 =
            FStar_List.fold_left
              (fun uu____3788  ->
                 fun uu____3789  ->
                   match (uu____3788, uu____3789) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3817 = is_C c in
                       if uu____3817
                       then
                         let xw =
                           let uu____3822 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3822 in
                         let x =
                           let uu___112_3824 = bv in
                           let uu____3825 =
                             let uu____3828 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3828 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___112_3824.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___112_3824.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3825
                           } in
                         let env3 =
                           let uu___113_3830 = env2 in
                           let uu____3831 =
                             let uu____3833 =
                               let uu____3834 =
                                 let uu____3839 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3839) in
                               FStar_Syntax_Syntax.NT uu____3834 in
                             uu____3833 :: (env2.subst) in
                           {
                             env = (uu___113_3830.env);
                             subst = uu____3831;
                             tc_const = (uu___113_3830.tc_const)
                           } in
                         let uu____3840 =
                           let uu____3842 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3843 =
                             let uu____3845 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3845 :: acc in
                           uu____3842 :: uu____3843 in
                         (env3, uu____3840)
                       else
                         (let x =
                            let uu___114_3849 = bv in
                            let uu____3850 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_3849.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_3849.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3850
                            } in
                          let uu____3853 =
                            let uu____3855 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3855 :: acc in
                          (env2, uu____3853))) (env1, []) binders1 in
          (match uu____3779 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3867 =
                 let check_what =
                   let uu____3879 = is_monadic what in
                   if uu____3879 then check_m else check_n in
                 let uu____3888 = check_what env2 body1 in
                 match uu____3888 with
                 | (t,s_body,u_body) ->
                     let uu____3898 =
                       let uu____3899 =
                         let uu____3900 = is_monadic what in
                         if uu____3900 then M t else N t in
                       comp_of_nm uu____3899 in
                     (uu____3898, s_body, u_body) in
               (match uu____3867 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3943 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___96_3945  ->
                                    match uu___96_3945 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3946 -> false)) in
                          if uu____3943
                          then
                            let double_starred_comp =
                              let uu____3954 =
                                let uu____3955 =
                                  let uu____3956 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____3956 in
                                FStar_All.pipe_left double_star uu____3955 in
                              FStar_Syntax_Syntax.mk_Total uu____3954 in
                            let flags =
                              FStar_List.filter
                                (fun uu___97_3961  ->
                                   match uu___97_3961 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3962 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____3963 =
                              let uu____3969 =
                                let uu____3970 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____3970 in
                              FStar_Util.Inl uu____3969 in
                            Some uu____3963
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___115_3990 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___115_3990.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___115_3990.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___115_3990.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____3991  ->
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
                          let uu____4008 =
                            let uu____4014 =
                              let uu____4018 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___98_4020  ->
                                        match uu___98_4020 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4021 -> false)) in
                              if uu____4018
                              then
                                let uu____4025 =
                                  FStar_List.filter
                                    (fun uu___99_4027  ->
                                       match uu___99_4027 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4028 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4025)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4014 in
                          Some uu____4008 in
                    let uu____4040 =
                      let comp1 =
                        let uu____4052 = is_monadic what in
                        let uu____4053 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4052 uu____4053 in
                      let uu____4054 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4054,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4040 with
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
                FStar_Syntax_Syntax.ty = uu____4132;
                FStar_Syntax_Syntax.p = uu____4133;_};
            FStar_Syntax_Syntax.fv_delta = uu____4134;
            FStar_Syntax_Syntax.fv_qual = uu____4135;_}
          ->
          let uu____4141 =
            let uu____4144 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4144 in
          (match uu____4141 with
           | (uu____4160,t) ->
               let uu____4162 = let uu____4163 = normalize1 t in N uu____4163 in
               (uu____4162, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4180 = check_n env head1 in
          (match uu____4180 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4194 =
                   let uu____4195 = FStar_Syntax_Subst.compress t in
                   uu____4195.FStar_Syntax_Syntax.n in
                 match uu____4194 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4198 -> true
                 | uu____4206 -> false in
               let rec flatten1 t =
                 let uu____4218 =
                   let uu____4219 = FStar_Syntax_Subst.compress t in
                   uu____4219.FStar_Syntax_Syntax.n in
                 match uu____4218 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4231);
                                FStar_Syntax_Syntax.tk = uu____4232;
                                FStar_Syntax_Syntax.pos = uu____4233;
                                FStar_Syntax_Syntax.vars = uu____4234;_})
                     when is_arrow t1 ->
                     let uu____4251 = flatten1 t1 in
                     (match uu____4251 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4303,uu____4304)
                     -> flatten1 e1
                 | uu____4333 ->
                     let uu____4334 =
                       let uu____4335 =
                         let uu____4336 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4336 in
                       FStar_Errors.Err uu____4335 in
                     raise uu____4334 in
               let uu____4344 = flatten1 t_head in
               (match uu____4344 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4396 =
                          let uu____4397 =
                            let uu____4398 = FStar_Util.string_of_int n1 in
                            let uu____4405 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4416 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4398 uu____4405 uu____4416 in
                          FStar_Errors.Err uu____4397 in
                        raise uu____4396)
                     else ();
                     (let uu____4424 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4424 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4451 args1 =
                            match uu____4451 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4494 =
                                       let uu____4495 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4495.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4494
                                 | (binders3,[]) ->
                                     let uu____4514 =
                                       let uu____4515 =
                                         let uu____4518 =
                                           let uu____4519 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4519 in
                                         FStar_Syntax_Subst.compress
                                           uu____4518 in
                                       uu____4515.FStar_Syntax_Syntax.n in
                                     (match uu____4514 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4535 =
                                            let uu____4536 =
                                              let uu____4537 =
                                                let uu____4545 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4545) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4537 in
                                            mk1 uu____4536 in
                                          N uu____4535
                                      | uu____4549 -> failwith "wat?")
                                 | ([],uu____4550::uu____4551) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4576)::binders3,(arg,uu____4579)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4613 = FStar_List.splitAt n' binders1 in
                          (match uu____4613 with
                           | (binders2,uu____4632) ->
                               let uu____4645 =
                                 let uu____4655 =
                                   FStar_List.map2
                                     (fun uu____4675  ->
                                        fun uu____4676  ->
                                          match (uu____4675, uu____4676) with
                                          | ((bv,uu____4693),(arg,q)) ->
                                              let uu____4700 =
                                                let uu____4701 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4701.FStar_Syntax_Syntax.n in
                                              (match uu____4700 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4711 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4724 ->
                                                   let uu____4725 =
                                                     check_n env arg in
                                                   (match uu____4725 with
                                                    | (uu____4736,s_arg,u_arg)
                                                        ->
                                                        let uu____4739 =
                                                          let uu____4743 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4743
                                                          then
                                                            let uu____4747 =
                                                              let uu____4750
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4750, q) in
                                                            [uu____4747;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4739))))
                                     binders2 args in
                                 FStar_List.split uu____4655 in
                               (match uu____4645 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4797 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4803 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4797, uu____4803)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4852) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4858) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4864,uu____4865) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4895 = let uu____4896 = env.tc_const c in N uu____4896 in
          (uu____4895, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4897 ->
          let uu____4905 =
            let uu____4906 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4906 in
          failwith uu____4905
      | FStar_Syntax_Syntax.Tm_type uu____4910 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4914 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4925 ->
          let uu____4930 =
            let uu____4931 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4931 in
          failwith uu____4930
      | FStar_Syntax_Syntax.Tm_uvar uu____4935 ->
          let uu____4944 =
            let uu____4945 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4945 in
          failwith uu____4944
      | FStar_Syntax_Syntax.Tm_delayed uu____4949 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4973 =
            let uu____4974 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4974 in
          failwith uu____4973
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
          let uu____5012 = check_n env e0 in
          match uu____5012 with
          | (uu____5019,s_e0,u_e0) ->
              let uu____5022 =
                let uu____5040 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5073 = FStar_Syntax_Subst.open_branch b in
                       match uu____5073 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___116_5105 = env in
                             let uu____5106 =
                               let uu____5107 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5107 in
                             {
                               env = uu____5106;
                               subst = (uu___116_5105.subst);
                               tc_const = (uu___116_5105.tc_const)
                             } in
                           let uu____5109 = f env1 body in
                           (match uu____5109 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5158 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5040 in
              (match uu____5022 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5223 = FStar_List.hd nms in
                     match uu____5223 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_5227  ->
                          match uu___100_5227 with
                          | M uu____5228 -> true
                          | uu____5229 -> false) nms in
                   let uu____5230 =
                     let uu____5253 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5305  ->
                              match uu____5305 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5428 =
                                         check env original_body (M t2) in
                                       (match uu____5428 with
                                        | (uu____5451,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5480,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5253 in
                   (match uu____5230 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5599  ->
                                 match uu____5599 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5640 =
                                         let uu____5641 =
                                           let uu____5651 =
                                             let uu____5655 =
                                               let uu____5658 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5659 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5658, uu____5659) in
                                             [uu____5655] in
                                           (s_body, uu____5651) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5641 in
                                       mk1 uu____5640 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5681 =
                              let uu____5682 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5682] in
                            let uu____5683 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5685 =
                              let uu____5692 =
                                let uu____5698 =
                                  let uu____5699 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5699 in
                                FStar_Util.Inl uu____5698 in
                              Some uu____5692 in
                            FStar_Syntax_Util.abs uu____5681 uu____5683
                              uu____5685 in
                          let t1_star =
                            let uu____5713 =
                              let uu____5717 =
                                let uu____5718 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5718 in
                              [uu____5717] in
                            let uu____5719 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5713 uu____5719 in
                          let uu____5722 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5752 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5722, uu____5752)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5766 =
                             let uu____5769 =
                               let uu____5770 =
                                 let uu____5788 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5788,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5770 in
                             mk1 uu____5769 in
                           let uu____5815 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5766, uu____5815))))
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
              let uu____5858 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5858] in
            let uu____5859 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5859 with
            | (x_binders1,e21) ->
                let uu____5867 = infer env e1 in
                (match uu____5867 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5878 = is_C t1 in
                       if uu____5878
                       then
                         let uu___117_5879 = binding in
                         let uu____5880 =
                           let uu____5883 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5883 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___117_5879.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___117_5879.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5880;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___117_5879.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___117_5879.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___118_5886 = env in
                       let uu____5887 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5888 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5888.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5888.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5887;
                         subst = (uu___118_5886.subst);
                         tc_const = (uu___118_5886.tc_const)
                       } in
                     let uu____5889 = proceed env1 e21 in
                     (match uu____5889 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___120_5900 = binding in
                            let uu____5901 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_5900.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___120_5900.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5901;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_5900.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___120_5900.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5904 =
                            let uu____5907 =
                              let uu____5908 =
                                let uu____5916 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___121_5921 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5921.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5921.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5921.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5921.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5916) in
                              FStar_Syntax_Syntax.Tm_let uu____5908 in
                            mk1 uu____5907 in
                          let uu____5922 =
                            let uu____5925 =
                              let uu____5926 =
                                let uu____5934 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___122_5939 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_5939.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_5939.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_5939.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_5939.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5934) in
                              FStar_Syntax_Syntax.Tm_let uu____5926 in
                            mk1 uu____5925 in
                          (nm_rec, uu____5904, uu____5922))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___123_5948 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___123_5948.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___123_5948.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___123_5948.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___124_5950 = env in
                       let uu____5951 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_5952 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_5952.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_5952.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5951;
                         subst = (uu___124_5950.subst);
                         tc_const = (uu___124_5950.tc_const)
                       } in
                     let uu____5953 = ensure_m env1 e21 in
                     (match uu____5953 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5970 =
                              let uu____5971 =
                                let uu____5981 =
                                  let uu____5985 =
                                    let uu____5988 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5989 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5988, uu____5989) in
                                  [uu____5985] in
                                (s_e2, uu____5981) in
                              FStar_Syntax_Syntax.Tm_app uu____5971 in
                            mk1 uu____5970 in
                          let s_e22 =
                            let uu____5998 =
                              let uu____6005 =
                                let uu____6011 =
                                  let uu____6012 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6012 in
                                FStar_Util.Inl uu____6011 in
                              Some uu____6005 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____5998 in
                          let body =
                            let uu____6026 =
                              let uu____6027 =
                                let uu____6037 =
                                  let uu____6041 =
                                    let uu____6044 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6044) in
                                  [uu____6041] in
                                (s_e1, uu____6037) in
                              FStar_Syntax_Syntax.Tm_app uu____6027 in
                            mk1 uu____6026 in
                          let uu____6052 =
                            let uu____6053 =
                              let uu____6054 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6054] in
                            let uu____6055 =
                              let uu____6062 =
                                let uu____6068 =
                                  let uu____6069 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6069 in
                                FStar_Util.Inl uu____6068 in
                              Some uu____6062 in
                            FStar_Syntax_Util.abs uu____6053 body uu____6055 in
                          let uu____6080 =
                            let uu____6083 =
                              let uu____6084 =
                                let uu____6092 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___126_6097 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_6097.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_6097.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_6097.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_6097.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6092) in
                              FStar_Syntax_Syntax.Tm_let uu____6084 in
                            mk1 uu____6083 in
                          ((M t2), uu____6052, uu____6080)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6106 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6106 in
      let uu____6111 = check env e mn in
      match uu____6111 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6121 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6134 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6134 in
      let uu____6139 = check env e mn in
      match uu____6139 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6149 -> failwith "[check_m]: impossible"
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
        (let uu____6171 =
           let uu____6172 = is_C c in Prims.op_Negation uu____6172 in
         if uu____6171 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6184 =
           let uu____6185 = FStar_Syntax_Subst.compress c in
           uu____6185.FStar_Syntax_Syntax.n in
         match uu____6184 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6204 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6204 with
              | (wp_head,wp_args) ->
                  ((let uu____6231 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6248 =
                           let uu____6249 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6249 in
                         Prims.op_Negation uu____6248) in
                    if uu____6231 then failwith "mismatch" else ());
                   (let uu____6261 =
                      let uu____6262 =
                        let uu____6272 =
                          FStar_List.map2
                            (fun uu____6282  ->
                               fun uu____6283  ->
                                 match (uu____6282, uu____6283) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6306 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6306
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6309 = print_implicit q in
                                         let uu____6310 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6309 uu____6310)
                                      else ();
                                      (let uu____6312 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6312, q)))) args wp_args in
                        (head1, uu____6272) in
                      FStar_Syntax_Syntax.Tm_app uu____6262 in
                    mk1 uu____6261)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6334 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6334 with
              | (binders_orig,comp1) ->
                  let uu____6339 =
                    let uu____6347 =
                      FStar_List.map
                        (fun uu____6361  ->
                           match uu____6361 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6374 = is_C h in
                               if uu____6374
                               then
                                 let w' =
                                   let uu____6381 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6381 in
                                 let uu____6382 =
                                   let uu____6386 =
                                     let uu____6390 =
                                       let uu____6393 =
                                         let uu____6394 =
                                           let uu____6395 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6395 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6394 in
                                       (uu____6393, q) in
                                     [uu____6390] in
                                   (w', q) :: uu____6386 in
                                 (w', uu____6382)
                               else
                                 (let x =
                                    let uu____6407 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6407 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6347 in
                  (match uu____6339 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6437 =
                           let uu____6439 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6439 in
                         FStar_Syntax_Subst.subst_comp uu____6437 comp1 in
                       let app =
                         let uu____6443 =
                           let uu____6444 =
                             let uu____6454 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6461 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6462 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6461, uu____6462)) bvs in
                             (wp, uu____6454) in
                           FStar_Syntax_Syntax.Tm_app uu____6444 in
                         mk1 uu____6443 in
                       let comp3 =
                         let uu____6467 = type_of_comp comp2 in
                         let uu____6468 = is_monadic_comp comp2 in
                         trans_G env uu____6467 uu____6468 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6470,uu____6471) ->
             trans_F_ env e wp
         | uu____6500 -> failwith "impossible trans_F_")
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
            let uu____6505 =
              let uu____6506 = star_type' env h in
              let uu____6509 =
                let uu____6515 =
                  let uu____6518 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6518) in
                [uu____6515] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6506;
                FStar_Syntax_Syntax.effect_args = uu____6509;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6505
          else
            (let uu____6524 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6524)
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
    fun t  -> let uu____6535 = n env.env t in star_type' env uu____6535
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6547 = n env.env t in check_n env uu____6547
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6557 = n env.env c in
        let uu____6558 = n env.env wp in trans_F_ env uu____6557 uu____6558