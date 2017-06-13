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
                             let uu____1500 =
                               let uu____1501 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1504 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1501 uu____1504 in
                             let uu____1507 =
                               let uu____1508 =
                                 let uu____1511 =
                                   let uu____1517 =
                                     let uu____1518 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1518 in
                                   [uu____1517] in
                                 FStar_Syntax_Util.mk_app x uu____1511 in
                               let uu____1519 =
                                 let uu____1522 =
                                   let uu____1528 =
                                     let uu____1529 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1529 in
                                   [uu____1528] in
                                 FStar_Syntax_Util.mk_app y uu____1522 in
                               mk_rel1 b uu____1508 uu____1519 in
                             FStar_Syntax_Util.mk_imp uu____1500 uu____1507 in
                           let uu____1530 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1530)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1533);
                                      FStar_Syntax_Syntax.tk = uu____1534;
                                      FStar_Syntax_Syntax.pos = uu____1535;
                                      FStar_Syntax_Syntax.vars = uu____1536;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1559 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1559
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1562 =
                              let uu____1565 =
                                let uu____1571 =
                                  let uu____1572 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1572 in
                                [uu____1571] in
                              FStar_Syntax_Util.mk_app x uu____1565 in
                            let uu____1573 =
                              let uu____1576 =
                                let uu____1582 =
                                  let uu____1583 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1583 in
                                [uu____1582] in
                              FStar_Syntax_Util.mk_app y uu____1576 in
                            mk_rel1 b uu____1562 uu____1573 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1590 =
                               let uu____1591 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1594 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1591 uu____1594 in
                             let uu____1597 =
                               let uu____1598 =
                                 let uu____1601 =
                                   let uu____1607 =
                                     let uu____1608 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1608 in
                                   [uu____1607] in
                                 FStar_Syntax_Util.mk_app x uu____1601 in
                               let uu____1609 =
                                 let uu____1612 =
                                   let uu____1618 =
                                     let uu____1619 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1619 in
                                   [uu____1618] in
                                 FStar_Syntax_Util.mk_app y uu____1612 in
                               mk_rel1 b uu____1598 uu____1609 in
                             FStar_Syntax_Util.mk_imp uu____1590 uu____1597 in
                           let uu____1620 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1620)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___102_1641 = t1 in
                          let uu____1642 =
                            let uu____1643 =
                              let uu____1651 =
                                let uu____1652 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1652 in
                              ([binder], uu____1651) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1643 in
                          {
                            FStar_Syntax_Syntax.n = uu____1642;
                            FStar_Syntax_Syntax.tk =
                              (uu___102_1641.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___102_1641.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___102_1641.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1664 ->
                        failwith "unhandled arrow"
                    | uu____1672 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1689 =
                        let uu____1690 = FStar_Syntax_Subst.compress t1 in
                        uu____1690.FStar_Syntax_Syntax.n in
                      match uu____1689 with
                      | FStar_Syntax_Syntax.Tm_type uu____1695 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1712 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1712
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1727 =
                                let uu____1728 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1728 i in
                              FStar_Syntax_Syntax.fvar uu____1727
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1752 =
                            let uu____1760 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1769  ->
                                     match uu____1769 with
                                     | (t2,q) ->
                                         let uu____1776 = project i x in
                                         let uu____1777 = project i y in
                                         mk_stronger t2 uu____1776 uu____1777)
                                args in
                            match uu____1760 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1752 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1824);
                                      FStar_Syntax_Syntax.tk = uu____1825;
                                      FStar_Syntax_Syntax.pos = uu____1826;
                                      FStar_Syntax_Syntax.vars = uu____1827;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1849  ->
                                   match uu____1849 with
                                   | (bv,q) ->
                                       let uu____1854 =
                                         let uu____1855 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1855 in
                                       FStar_Syntax_Syntax.gen_bv uu____1854
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1859 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1859) bvs in
                          let body =
                            let uu____1863 = FStar_Syntax_Util.mk_app x args in
                            let uu____1864 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1863 uu____1864 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1869);
                                      FStar_Syntax_Syntax.tk = uu____1870;
                                      FStar_Syntax_Syntax.pos = uu____1871;
                                      FStar_Syntax_Syntax.vars = uu____1872;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1894  ->
                                   match uu____1894 with
                                   | (bv,q) ->
                                       let uu____1899 =
                                         let uu____1900 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1900 in
                                       FStar_Syntax_Syntax.gen_bv uu____1899
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1904 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1904) bvs in
                          let body =
                            let uu____1908 = FStar_Syntax_Util.mk_app x args in
                            let uu____1909 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1908 uu____1909 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1912 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1918 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1919 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1920 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1918 uu____1919 uu____1920 in
                    let uu____1921 =
                      let uu____1922 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1922 in
                    FStar_Syntax_Util.abs uu____1921 body ret_tot_type in
                  let stronger1 =
                    let uu____1937 = mk_lid "stronger" in
                    register env1 uu____1937 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1943 = FStar_Util.prefix gamma in
                    match uu____1943 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1969 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1969 in
                          let uu____1972 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1972 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1980 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1980 in
                              let guard_free1 =
                                let uu____1987 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1987 in
                              let pat =
                                let uu____1991 =
                                  let uu____1997 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1997] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1991 in
                              let pattern_guarded_body =
                                let uu____2001 =
                                  let uu____2002 =
                                    let uu____2007 =
                                      let uu____2008 =
                                        let uu____2015 =
                                          let uu____2017 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2017] in
                                        [uu____2015] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2008 in
                                    (body, uu____2007) in
                                  FStar_Syntax_Syntax.Tm_meta uu____2002 in
                                mk1 uu____2001 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2020 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2023 =
                            let uu____2024 =
                              let uu____2025 =
                                let uu____2026 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2029 =
                                  let uu____2035 = args_of_binders1 wp_args in
                                  let uu____2037 =
                                    let uu____2039 =
                                      let uu____2040 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2040 in
                                    [uu____2039] in
                                  FStar_List.append uu____2035 uu____2037 in
                                FStar_Syntax_Util.mk_app uu____2026
                                  uu____2029 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2025 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2024 in
                          FStar_Syntax_Util.abs gamma uu____2023
                            ret_gtot_type in
                        let uu____2041 =
                          let uu____2042 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2042 in
                        FStar_Syntax_Util.abs uu____2041 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2049 = mk_lid "wp_ite" in
                    register env1 uu____2049 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2055 = FStar_Util.prefix gamma in
                    match uu____2055 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2079 =
                            let uu____2080 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2083 =
                              let uu____2089 =
                                let uu____2090 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2090 in
                              [uu____2089] in
                            FStar_Syntax_Util.mk_app uu____2080 uu____2083 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2079 in
                        let uu____2091 =
                          let uu____2092 =
                            let uu____2096 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2096 gamma in
                          FStar_List.append binders uu____2092 in
                        FStar_Syntax_Util.abs uu____2091 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2105 = mk_lid "null_wp" in
                    register env1 uu____2105 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2114 =
                        let uu____2120 =
                          let uu____2122 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2123 =
                            let uu____2125 =
                              let uu____2128 =
                                let uu____2134 =
                                  let uu____2135 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2135 in
                                [uu____2134] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2128 in
                            let uu____2136 =
                              let uu____2140 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2140] in
                            uu____2125 :: uu____2136 in
                          uu____2122 :: uu____2123 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2120 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2114 in
                    let uu____2143 =
                      let uu____2144 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2144 in
                    FStar_Syntax_Util.abs uu____2143 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2151 = mk_lid "wp_trivial" in
                    register env1 uu____2151 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2156 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2156
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2161 =
                      let uu____2163 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2163 in
                    let uu____2168 =
                      let uu___103_2169 = ed in
                      let uu____2170 =
                        let uu____2171 = c wp_if_then_else2 in
                        ([], uu____2171) in
                      let uu____2173 =
                        let uu____2174 = c wp_ite2 in ([], uu____2174) in
                      let uu____2176 =
                        let uu____2177 = c stronger2 in ([], uu____2177) in
                      let uu____2179 =
                        let uu____2180 = c wp_close2 in ([], uu____2180) in
                      let uu____2182 =
                        let uu____2183 = c wp_assert2 in ([], uu____2183) in
                      let uu____2185 =
                        let uu____2186 = c wp_assume2 in ([], uu____2186) in
                      let uu____2188 =
                        let uu____2189 = c null_wp2 in ([], uu____2189) in
                      let uu____2191 =
                        let uu____2192 = c wp_trivial2 in ([], uu____2192) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_2169.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_2169.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_2169.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_2169.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_2169.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_2169.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_2169.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2170;
                        FStar_Syntax_Syntax.ite_wp = uu____2173;
                        FStar_Syntax_Syntax.stronger = uu____2176;
                        FStar_Syntax_Syntax.close_wp = uu____2179;
                        FStar_Syntax_Syntax.assert_p = uu____2182;
                        FStar_Syntax_Syntax.assume_p = uu____2185;
                        FStar_Syntax_Syntax.null_wp = uu____2188;
                        FStar_Syntax_Syntax.trivial = uu____2191;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_2169.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_2169.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_2169.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_2169.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2161, uu____2168)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_2204 = dmff_env in
      {
        env = env';
        subst = (uu___104_2204.subst);
        tc_const = (uu___104_2204.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2217 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2229 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___90_2239  ->
    match uu___90_2239 with
    | FStar_Syntax_Syntax.Total (t,uu____2241) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___89_2250  ->
                match uu___89_2250 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2251 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2253 =
          let uu____2254 =
            let uu____2255 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2255 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2254 in
        failwith uu____2253
    | FStar_Syntax_Syntax.GTotal uu____2256 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___91_2264  ->
    match uu___91_2264 with
    | N t ->
        let uu____2266 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2266
    | M t ->
        let uu____2268 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2268
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2272,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2274;
                      FStar_Syntax_Syntax.pos = uu____2275;
                      FStar_Syntax_Syntax.vars = uu____2276;_})
        -> nm_of_comp n2
    | uu____2287 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2299 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2299 with | M uu____2300 -> true | N uu____2301 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2305 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2315 =
        let uu____2319 =
          let uu____2320 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2320 in
        [uu____2319] in
      let uu____2321 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2315 uu____2321 in
    let uu____2324 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2324
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
          (let uu____2359 =
             let uu____2367 =
               let uu____2371 =
                 let uu____2374 =
                   let uu____2375 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2375 in
                 let uu____2376 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2374, uu____2376) in
               [uu____2371] in
             let uu____2381 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2367, uu____2381) in
           FStar_Syntax_Syntax.Tm_arrow uu____2359)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2410) ->
          let binders1 =
            FStar_List.map
              (fun uu____2429  ->
                 match uu____2429 with
                 | (bv,aqual) ->
                     let uu____2436 =
                       let uu___105_2437 = bv in
                       let uu____2438 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_2437.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_2437.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2438
                       } in
                     (uu____2436, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2441,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2443);
                             FStar_Syntax_Syntax.tk = uu____2444;
                             FStar_Syntax_Syntax.pos = uu____2445;
                             FStar_Syntax_Syntax.vars = uu____2446;_})
               ->
               let uu____2463 =
                 let uu____2464 =
                   let uu____2472 =
                     let uu____2473 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2473 in
                   (binders1, uu____2472) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2464 in
               mk1 uu____2463
           | uu____2477 ->
               let uu____2478 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2478 with
                | N hn ->
                    let uu____2480 =
                      let uu____2481 =
                        let uu____2489 =
                          let uu____2490 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2490 in
                        (binders1, uu____2489) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2481 in
                    mk1 uu____2480
                | M a ->
                    let uu____2495 =
                      let uu____2496 =
                        let uu____2504 =
                          let uu____2508 =
                            let uu____2512 =
                              let uu____2515 =
                                let uu____2516 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2516 in
                              let uu____2517 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2515, uu____2517) in
                            [uu____2512] in
                          FStar_List.append binders1 uu____2508 in
                        let uu____2524 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2504, uu____2524) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2496 in
                    mk1 uu____2495))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2575 = f x in
                    FStar_Util.string_builder_append strb uu____2575);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2579 = f x1 in
                         FStar_Util.string_builder_append strb uu____2579))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2581 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2582 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2581 uu____2582 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2590 =
              let uu____2591 = FStar_Syntax_Subst.compress ty in
              uu____2591.FStar_Syntax_Syntax.n in
            match uu____2590 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2606 =
                  let uu____2607 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2607 in
                if uu____2606
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2621 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2621 s in
                       let uu____2623 =
                         let uu____2624 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2624 in
                       if uu____2623
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2627 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2627 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2638  ->
                                  match uu____2638 with
                                  | (bv,uu____2644) ->
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
            | uu____2659 ->
                ((let uu____2661 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2661);
                 false) in
          let rec is_valid_application head2 =
            let uu____2666 =
              let uu____2667 = FStar_Syntax_Subst.compress head2 in
              uu____2667.FStar_Syntax_Syntax.n in
            match uu____2666 with
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
                  (let uu____2671 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2671)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2686 -> true
                 | uu____2696 ->
                     ((let uu____2698 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2698);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2699 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2700 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2702) ->
                is_valid_application t2
            | uu____2707 -> false in
          let uu____2708 = is_valid_application head1 in
          if uu____2708
          then
            let uu____2709 =
              let uu____2710 =
                let uu____2720 =
                  FStar_List.map
                    (fun uu____2730  ->
                       match uu____2730 with
                       | (t2,qual) ->
                           let uu____2743 = star_type' env t2 in
                           (uu____2743, qual)) args in
                (head1, uu____2720) in
              FStar_Syntax_Syntax.Tm_app uu____2710 in
            mk1 uu____2709
          else
            (let uu____2750 =
               let uu____2751 =
                 let uu____2752 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2752 in
               FStar_Errors.Err uu____2751 in
             raise uu____2750)
      | FStar_Syntax_Syntax.Tm_bvar uu____2753 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2754 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2755 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2756 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2782 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2782 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___108_2788 = env in
                 let uu____2789 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2789;
                   subst = (uu___108_2788.subst);
                   tc_const = (uu___108_2788.tc_const)
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
               ((let uu___109_2806 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_2806.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_2806.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2813 =
            let uu____2814 =
              let uu____2819 = star_type' env t2 in (uu____2819, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2814 in
          mk1 uu____2813
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2857 =
            let uu____2858 =
              let uu____2876 = star_type' env e in
              let uu____2877 =
                let uu____2887 =
                  let uu____2892 = star_type' env t2 in
                  FStar_Util.Inl uu____2892 in
                (uu____2887, None) in
              (uu____2876, uu____2877, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2858 in
          mk1 uu____2857
      | FStar_Syntax_Syntax.Tm_ascribed uu____2914 ->
          let uu____2932 =
            let uu____2933 =
              let uu____2934 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2934 in
            FStar_Errors.Err uu____2933 in
          raise uu____2932
      | FStar_Syntax_Syntax.Tm_refine uu____2935 ->
          let uu____2940 =
            let uu____2941 =
              let uu____2942 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2942 in
            FStar_Errors.Err uu____2941 in
          raise uu____2940
      | FStar_Syntax_Syntax.Tm_uinst uu____2943 ->
          let uu____2948 =
            let uu____2949 =
              let uu____2950 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2950 in
            FStar_Errors.Err uu____2949 in
          raise uu____2948
      | FStar_Syntax_Syntax.Tm_constant uu____2951 ->
          let uu____2952 =
            let uu____2953 =
              let uu____2954 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2954 in
            FStar_Errors.Err uu____2953 in
          raise uu____2952
      | FStar_Syntax_Syntax.Tm_match uu____2955 ->
          let uu____2971 =
            let uu____2972 =
              let uu____2973 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2973 in
            FStar_Errors.Err uu____2972 in
          raise uu____2971
      | FStar_Syntax_Syntax.Tm_let uu____2974 ->
          let uu____2982 =
            let uu____2983 =
              let uu____2984 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2984 in
            FStar_Errors.Err uu____2983 in
          raise uu____2982
      | FStar_Syntax_Syntax.Tm_uvar uu____2985 ->
          let uu____2994 =
            let uu____2995 =
              let uu____2996 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2996 in
            FStar_Errors.Err uu____2995 in
          raise uu____2994
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2997 =
            let uu____2998 =
              let uu____2999 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2999 in
            FStar_Errors.Err uu____2998 in
          raise uu____2997
      | FStar_Syntax_Syntax.Tm_delayed uu____3000 -> failwith "impossible"
let is_monadic uu___93_3033 =
  match uu___93_3033 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3045;
        FStar_Syntax_Syntax.res_typ = uu____3046;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3048;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3065  ->
              match uu___92_3065 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3066 -> false))
  | Some (FStar_Util.Inr (uu____3067,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3080  ->
              match uu___92_3080 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3081 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3085 =
      let uu____3086 = FStar_Syntax_Subst.compress t in
      uu____3086.FStar_Syntax_Syntax.n in
    match uu____3085 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3106 =
            let uu____3107 = FStar_List.hd args in fst uu____3107 in
          is_C uu____3106 in
        if r
        then
          ((let uu____3119 =
              let uu____3120 =
                FStar_List.for_all
                  (fun uu____3123  ->
                     match uu____3123 with | (h,uu____3127) -> is_C h) args in
              Prims.op_Negation uu____3120 in
            if uu____3119 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3131 =
              let uu____3132 =
                FStar_List.for_all
                  (fun uu____3135  ->
                     match uu____3135 with
                     | (h,uu____3139) ->
                         let uu____3140 = is_C h in
                         Prims.op_Negation uu____3140) args in
              Prims.op_Negation uu____3132 in
            if uu____3131 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3154 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3154 with
         | M t1 ->
             ((let uu____3157 = is_C t1 in
               if uu____3157 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3161) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3167) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3173,uu____3174) -> is_C t1
    | uu____3203 -> false
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
          let uu____3230 =
            let uu____3231 =
              let uu____3241 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3242 =
                let uu____3246 =
                  let uu____3249 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3249) in
                [uu____3246] in
              (uu____3241, uu____3242) in
            FStar_Syntax_Syntax.Tm_app uu____3231 in
          mk1 uu____3230 in
        let uu____3257 =
          let uu____3258 = FStar_Syntax_Syntax.mk_binder p in [uu____3258] in
        let uu____3259 =
          let uu____3266 =
            let uu____3272 =
              let uu____3273 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3273 in
            FStar_Util.Inl uu____3272 in
          Some uu____3266 in
        FStar_Syntax_Util.abs uu____3257 body uu____3259
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___94_3286  ->
    match uu___94_3286 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3287 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
        let return_if uu____3431 =
          match uu____3431 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3452 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3453 =
                       let uu____3454 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3454 in
                     Prims.op_Negation uu____3453) in
                if uu____3452
                then
                  let uu____3455 =
                    let uu____3456 =
                      let uu____3457 = FStar_Syntax_Print.term_to_string e in
                      let uu____3458 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3459 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3457 uu____3458 uu____3459 in
                    FStar_Errors.Err uu____3456 in
                  raise uu____3455
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3473 = mk_return env t1 s_e in
                     ((M t1), uu____3473, u_e)))
               | (M t1,N t2) ->
                   let uu____3476 =
                     let uu____3477 =
                       let uu____3478 = FStar_Syntax_Print.term_to_string e in
                       let uu____3479 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3480 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3478 uu____3479 uu____3480 in
                     FStar_Errors.Err uu____3477 in
                   raise uu____3476) in
        let ensure_m env1 e2 =
          let strip_m uu___95_3506 =
            match uu___95_3506 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3516 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3527 =
                let uu____3528 =
                  let uu____3531 =
                    let uu____3532 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3532 in
                  (uu____3531, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3528 in
              raise uu____3527
          | M uu____3536 ->
              let uu____3537 = check env1 e2 context_nm in strip_m uu____3537 in
        let uu____3541 =
          let uu____3542 = FStar_Syntax_Subst.compress e in
          uu____3542.FStar_Syntax_Syntax.n in
        match uu____3541 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3548 ->
            let uu____3549 = infer env e in return_if uu____3549
        | FStar_Syntax_Syntax.Tm_name uu____3553 ->
            let uu____3554 = infer env e in return_if uu____3554
        | FStar_Syntax_Syntax.Tm_fvar uu____3558 ->
            let uu____3559 = infer env e in return_if uu____3559
        | FStar_Syntax_Syntax.Tm_abs uu____3563 ->
            let uu____3578 = infer env e in return_if uu____3578
        | FStar_Syntax_Syntax.Tm_constant uu____3582 ->
            let uu____3583 = infer env e in return_if uu____3583
        | FStar_Syntax_Syntax.Tm_app uu____3587 ->
            let uu____3597 = infer env e in return_if uu____3597
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3644) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3650) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3656,uu____3657) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3686 ->
            let uu____3694 =
              let uu____3695 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3695 in
            failwith uu____3694
        | FStar_Syntax_Syntax.Tm_type uu____3699 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3703 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3714 ->
            let uu____3719 =
              let uu____3720 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3720 in
            failwith uu____3719
        | FStar_Syntax_Syntax.Tm_uvar uu____3724 ->
            let uu____3733 =
              let uu____3734 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3734 in
            failwith uu____3733
        | FStar_Syntax_Syntax.Tm_delayed uu____3738 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3762 =
              let uu____3763 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3763 in
            failwith uu____3762
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
      let uu____3785 =
        let uu____3786 = FStar_Syntax_Subst.compress e in
        uu____3786.FStar_Syntax_Syntax.n in
      match uu____3785 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___110_3826 = env in
            let uu____3827 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3827;
              subst = (uu___110_3826.subst);
              tc_const = (uu___110_3826.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3836  ->
                 match uu____3836 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___111_3844 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___111_3844.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___111_3844.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3845 =
            FStar_List.fold_left
              (fun uu____3854  ->
                 fun uu____3855  ->
                   match (uu____3854, uu____3855) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3883 = is_C c in
                       if uu____3883
                       then
                         let xw =
                           let uu____3888 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3888 in
                         let x =
                           let uu___112_3890 = bv in
                           let uu____3891 =
                             let uu____3894 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3894 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___112_3890.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___112_3890.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3891
                           } in
                         let env3 =
                           let uu___113_3896 = env2 in
                           let uu____3897 =
                             let uu____3899 =
                               let uu____3900 =
                                 let uu____3905 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3905) in
                               FStar_Syntax_Syntax.NT uu____3900 in
                             uu____3899 :: (env2.subst) in
                           {
                             env = (uu___113_3896.env);
                             subst = uu____3897;
                             tc_const = (uu___113_3896.tc_const)
                           } in
                         let uu____3906 =
                           let uu____3908 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3909 =
                             let uu____3911 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3911 :: acc in
                           uu____3908 :: uu____3909 in
                         (env3, uu____3906)
                       else
                         (let x =
                            let uu___114_3915 = bv in
                            let uu____3916 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_3915.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_3915.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3916
                            } in
                          let uu____3919 =
                            let uu____3921 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3921 :: acc in
                          (env2, uu____3919))) (env1, []) binders1 in
          (match uu____3845 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3933 =
                 let check_what =
                   let uu____3945 = is_monadic what in
                   if uu____3945 then check_m else check_n in
                 let uu____3954 = check_what env2 body1 in
                 match uu____3954 with
                 | (t,s_body,u_body) ->
                     let uu____3964 =
                       let uu____3965 =
                         let uu____3966 = is_monadic what in
                         if uu____3966 then M t else N t in
                       comp_of_nm uu____3965 in
                     (uu____3964, s_body, u_body) in
               (match uu____3933 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____4009 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___96_4011  ->
                                    match uu___96_4011 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____4012 -> false)) in
                          if uu____4009
                          then
                            let double_starred_comp =
                              let uu____4020 =
                                let uu____4021 =
                                  let uu____4022 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____4022 in
                                FStar_All.pipe_left double_star uu____4021 in
                              FStar_Syntax_Syntax.mk_Total uu____4020 in
                            let flags =
                              FStar_List.filter
                                (fun uu___97_4027  ->
                                   match uu___97_4027 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____4028 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____4029 =
                              let uu____4035 =
                                let uu____4036 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____4036 in
                              FStar_Util.Inl uu____4035 in
                            Some uu____4029
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___115_4056 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___115_4056.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___115_4056.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___115_4056.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4057  ->
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
                          let uu____4074 =
                            let uu____4080 =
                              let uu____4084 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___98_4086  ->
                                        match uu___98_4086 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4087 -> false)) in
                              if uu____4084
                              then
                                let uu____4091 =
                                  FStar_List.filter
                                    (fun uu___99_4093  ->
                                       match uu___99_4093 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4094 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4091)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4080 in
                          Some uu____4074 in
                    let uu____4106 =
                      let comp1 =
                        let uu____4118 = is_monadic what in
                        let uu____4119 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4118 uu____4119 in
                      let uu____4120 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4120,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4106 with
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
                FStar_Syntax_Syntax.ty = uu____4198;
                FStar_Syntax_Syntax.p = uu____4199;_};
            FStar_Syntax_Syntax.fv_delta = uu____4200;
            FStar_Syntax_Syntax.fv_qual = uu____4201;_}
          ->
          let uu____4207 =
            let uu____4210 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4210 in
          (match uu____4207 with
           | (uu____4226,t) ->
               let uu____4228 = let uu____4229 = normalize1 t in N uu____4229 in
               (uu____4228, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4246 = check_n env head1 in
          (match uu____4246 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4260 =
                   let uu____4261 = FStar_Syntax_Subst.compress t in
                   uu____4261.FStar_Syntax_Syntax.n in
                 match uu____4260 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4264 -> true
                 | uu____4272 -> false in
               let rec flatten1 t =
                 let uu____4284 =
                   let uu____4285 = FStar_Syntax_Subst.compress t in
                   uu____4285.FStar_Syntax_Syntax.n in
                 match uu____4284 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4297);
                                FStar_Syntax_Syntax.tk = uu____4298;
                                FStar_Syntax_Syntax.pos = uu____4299;
                                FStar_Syntax_Syntax.vars = uu____4300;_})
                     when is_arrow t1 ->
                     let uu____4317 = flatten1 t1 in
                     (match uu____4317 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4369,uu____4370)
                     -> flatten1 e1
                 | uu____4399 ->
                     let uu____4400 =
                       let uu____4401 =
                         let uu____4402 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4402 in
                       FStar_Errors.Err uu____4401 in
                     raise uu____4400 in
               let uu____4410 = flatten1 t_head in
               (match uu____4410 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4462 =
                          let uu____4463 =
                            let uu____4464 = FStar_Util.string_of_int n1 in
                            let uu____4471 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4482 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4464 uu____4471 uu____4482 in
                          FStar_Errors.Err uu____4463 in
                        raise uu____4462)
                     else ();
                     (let uu____4490 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4490 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4517 args1 =
                            match uu____4517 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4560 =
                                       let uu____4561 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4561.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4560
                                 | (binders3,[]) ->
                                     let uu____4580 =
                                       let uu____4581 =
                                         let uu____4584 =
                                           let uu____4585 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4585 in
                                         FStar_Syntax_Subst.compress
                                           uu____4584 in
                                       uu____4581.FStar_Syntax_Syntax.n in
                                     (match uu____4580 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4601 =
                                            let uu____4602 =
                                              let uu____4603 =
                                                let uu____4611 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4611) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4603 in
                                            mk1 uu____4602 in
                                          N uu____4601
                                      | uu____4615 -> failwith "wat?")
                                 | ([],uu____4616::uu____4617) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4642)::binders3,(arg,uu____4645)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4679 = FStar_List.splitAt n' binders1 in
                          (match uu____4679 with
                           | (binders2,uu____4698) ->
                               let uu____4711 =
                                 let uu____4721 =
                                   FStar_List.map2
                                     (fun uu____4741  ->
                                        fun uu____4742  ->
                                          match (uu____4741, uu____4742) with
                                          | ((bv,uu____4759),(arg,q)) ->
                                              let uu____4766 =
                                                let uu____4767 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4767.FStar_Syntax_Syntax.n in
                                              (match uu____4766 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4777 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4790 ->
                                                   let uu____4791 =
                                                     check_n env arg in
                                                   (match uu____4791 with
                                                    | (uu____4802,s_arg,u_arg)
                                                        ->
                                                        let uu____4805 =
                                                          let uu____4809 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4809
                                                          then
                                                            let uu____4813 =
                                                              let uu____4816
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4816, q) in
                                                            [uu____4813;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4805))))
                                     binders2 args in
                                 FStar_List.split uu____4721 in
                               (match uu____4711 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4863 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4869 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4863, uu____4869)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4918) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4924) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4930,uu____4931) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4961 = let uu____4962 = env.tc_const c in N uu____4962 in
          (uu____4961, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4963 ->
          let uu____4971 =
            let uu____4972 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4972 in
          failwith uu____4971
      | FStar_Syntax_Syntax.Tm_type uu____4976 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4980 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4991 ->
          let uu____4996 =
            let uu____4997 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4997 in
          failwith uu____4996
      | FStar_Syntax_Syntax.Tm_uvar uu____5001 ->
          let uu____5010 =
            let uu____5011 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____5011 in
          failwith uu____5010
      | FStar_Syntax_Syntax.Tm_delayed uu____5015 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5039 =
            let uu____5040 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____5040 in
          failwith uu____5039
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
          let uu____5078 = check_n env e0 in
          match uu____5078 with
          | (uu____5085,s_e0,u_e0) ->
              let uu____5088 =
                let uu____5106 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5139 = FStar_Syntax_Subst.open_branch b in
                       match uu____5139 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___116_5171 = env in
                             let uu____5172 =
                               let uu____5173 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5173 in
                             {
                               env = uu____5172;
                               subst = (uu___116_5171.subst);
                               tc_const = (uu___116_5171.tc_const)
                             } in
                           let uu____5175 = f env1 body in
                           (match uu____5175 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5224 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5106 in
              (match uu____5088 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5289 = FStar_List.hd nms in
                     match uu____5289 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_5293  ->
                          match uu___100_5293 with
                          | M uu____5294 -> true
                          | uu____5295 -> false) nms in
                   let uu____5296 =
                     let uu____5319 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5371  ->
                              match uu____5371 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5494 =
                                         check env original_body (M t2) in
                                       (match uu____5494 with
                                        | (uu____5517,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5546,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5319 in
                   (match uu____5296 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5665  ->
                                 match uu____5665 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5706 =
                                         let uu____5707 =
                                           let uu____5717 =
                                             let uu____5721 =
                                               let uu____5724 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5725 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5724, uu____5725) in
                                             [uu____5721] in
                                           (s_body, uu____5717) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5707 in
                                       mk1 uu____5706 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5747 =
                              let uu____5748 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5748] in
                            let uu____5749 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5751 =
                              let uu____5758 =
                                let uu____5764 =
                                  let uu____5765 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5765 in
                                FStar_Util.Inl uu____5764 in
                              Some uu____5758 in
                            FStar_Syntax_Util.abs uu____5747 uu____5749
                              uu____5751 in
                          let t1_star =
                            let uu____5779 =
                              let uu____5783 =
                                let uu____5784 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5784 in
                              [uu____5783] in
                            let uu____5785 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5779 uu____5785 in
                          let uu____5788 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5818 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5788, uu____5818)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5832 =
                             let uu____5835 =
                               let uu____5836 =
                                 let uu____5854 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5854,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5836 in
                             mk1 uu____5835 in
                           let uu____5881 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5832, uu____5881))))
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
              let uu____5924 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5924] in
            let uu____5925 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5925 with
            | (x_binders1,e21) ->
                let uu____5933 = infer env e1 in
                (match uu____5933 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5944 = is_C t1 in
                       if uu____5944
                       then
                         let uu___117_5945 = binding in
                         let uu____5946 =
                           let uu____5949 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5949 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___117_5945.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___117_5945.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5946;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___117_5945.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___117_5945.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___118_5952 = env in
                       let uu____5953 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5954 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5954.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5954.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5953;
                         subst = (uu___118_5952.subst);
                         tc_const = (uu___118_5952.tc_const)
                       } in
                     let uu____5955 = proceed env1 e21 in
                     (match uu____5955 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___120_5966 = binding in
                            let uu____5967 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_5966.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___120_5966.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5967;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_5966.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___120_5966.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5970 =
                            let uu____5973 =
                              let uu____5974 =
                                let uu____5982 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___121_5987 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5987.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5987.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5987.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5987.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5982) in
                              FStar_Syntax_Syntax.Tm_let uu____5974 in
                            mk1 uu____5973 in
                          let uu____5988 =
                            let uu____5991 =
                              let uu____5992 =
                                let uu____6000 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___122_6005 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_6005.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_6005.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_6005.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_6005.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6000) in
                              FStar_Syntax_Syntax.Tm_let uu____5992 in
                            mk1 uu____5991 in
                          (nm_rec, uu____5970, uu____5988))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___123_6014 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___123_6014.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___123_6014.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___123_6014.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___124_6016 = env in
                       let uu____6017 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_6018 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_6018.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_6018.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____6017;
                         subst = (uu___124_6016.subst);
                         tc_const = (uu___124_6016.tc_const)
                       } in
                     let uu____6019 = ensure_m env1 e21 in
                     (match uu____6019 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____6036 =
                              let uu____6037 =
                                let uu____6047 =
                                  let uu____6051 =
                                    let uu____6054 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6055 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6054, uu____6055) in
                                  [uu____6051] in
                                (s_e2, uu____6047) in
                              FStar_Syntax_Syntax.Tm_app uu____6037 in
                            mk1 uu____6036 in
                          let s_e22 =
                            let uu____6064 =
                              let uu____6071 =
                                let uu____6077 =
                                  let uu____6078 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6078 in
                                FStar_Util.Inl uu____6077 in
                              Some uu____6071 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6064 in
                          let body =
                            let uu____6092 =
                              let uu____6093 =
                                let uu____6103 =
                                  let uu____6107 =
                                    let uu____6110 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6110) in
                                  [uu____6107] in
                                (s_e1, uu____6103) in
                              FStar_Syntax_Syntax.Tm_app uu____6093 in
                            mk1 uu____6092 in
                          let uu____6118 =
                            let uu____6119 =
                              let uu____6120 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6120] in
                            let uu____6121 =
                              let uu____6128 =
                                let uu____6134 =
                                  let uu____6135 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6135 in
                                FStar_Util.Inl uu____6134 in
                              Some uu____6128 in
                            FStar_Syntax_Util.abs uu____6119 body uu____6121 in
                          let uu____6146 =
                            let uu____6149 =
                              let uu____6150 =
                                let uu____6158 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___126_6163 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_6163.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_6163.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_6163.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_6163.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6158) in
                              FStar_Syntax_Syntax.Tm_let uu____6150 in
                            mk1 uu____6149 in
                          ((M t2), uu____6118, uu____6146)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6172 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6172 in
      let uu____6177 = check env e mn in
      match uu____6177 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6187 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6200 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6200 in
      let uu____6205 = check env e mn in
      match uu____6205 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6215 -> failwith "[check_m]: impossible"
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
        (let uu____6237 =
           let uu____6238 = is_C c in Prims.op_Negation uu____6238 in
         if uu____6237 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6250 =
           let uu____6251 = FStar_Syntax_Subst.compress c in
           uu____6251.FStar_Syntax_Syntax.n in
         match uu____6250 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6270 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6270 with
              | (wp_head,wp_args) ->
                  ((let uu____6297 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6314 =
                           let uu____6315 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6315 in
                         Prims.op_Negation uu____6314) in
                    if uu____6297 then failwith "mismatch" else ());
                   (let uu____6327 =
                      let uu____6328 =
                        let uu____6338 =
                          FStar_List.map2
                            (fun uu____6348  ->
                               fun uu____6349  ->
                                 match (uu____6348, uu____6349) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6372 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6372
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6375 = print_implicit q in
                                         let uu____6376 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6375 uu____6376)
                                      else ();
                                      (let uu____6378 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6378, q)))) args wp_args in
                        (head1, uu____6338) in
                      FStar_Syntax_Syntax.Tm_app uu____6328 in
                    mk1 uu____6327)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6400 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6400 with
              | (binders_orig,comp1) ->
                  let uu____6405 =
                    let uu____6413 =
                      FStar_List.map
                        (fun uu____6427  ->
                           match uu____6427 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6440 = is_C h in
                               if uu____6440
                               then
                                 let w' =
                                   let uu____6447 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6447 in
                                 let uu____6448 =
                                   let uu____6452 =
                                     let uu____6456 =
                                       let uu____6459 =
                                         let uu____6460 =
                                           let uu____6461 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6461 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6460 in
                                       (uu____6459, q) in
                                     [uu____6456] in
                                   (w', q) :: uu____6452 in
                                 (w', uu____6448)
                               else
                                 (let x =
                                    let uu____6473 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6473 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6413 in
                  (match uu____6405 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6503 =
                           let uu____6505 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6505 in
                         FStar_Syntax_Subst.subst_comp uu____6503 comp1 in
                       let app =
                         let uu____6509 =
                           let uu____6510 =
                             let uu____6520 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6527 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6528 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6527, uu____6528)) bvs in
                             (wp, uu____6520) in
                           FStar_Syntax_Syntax.Tm_app uu____6510 in
                         mk1 uu____6509 in
                       let comp3 =
                         let uu____6533 = type_of_comp comp2 in
                         let uu____6534 = is_monadic_comp comp2 in
                         trans_G env uu____6533 uu____6534 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6536,uu____6537) ->
             trans_F_ env e wp
         | uu____6566 -> failwith "impossible trans_F_")
and trans_G:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          let mk1 x = FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos in
          if is_monadic1
          then
            let uu____6581 =
              let uu____6582 = star_type' env h in
              let uu____6585 =
                let uu____6591 =
                  let uu____6594 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6594) in
                [uu____6591] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6582;
                FStar_Syntax_Syntax.effect_args = uu____6585;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6581
          else
            (let uu____6600 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6600)
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
    fun t  -> let uu____6611 = n env.env t in star_type' env uu____6611
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6623 = n env.env t in check_n env uu____6623
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6633 = n env.env c in
        let uu____6634 = n env.env wp in trans_F_ env uu____6633 uu____6634