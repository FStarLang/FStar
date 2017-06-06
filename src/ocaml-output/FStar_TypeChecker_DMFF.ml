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
                      let uu____954 =
                        let uu____955 =
                          let uu____965 = args_of_binders1 binders in
                          (c, uu____965) in
                        FStar_Syntax_Syntax.Tm_app uu____955 in
                      mk1 uu____954
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____973 =
                        let uu____974 =
                          let uu____978 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____979 =
                            let uu____981 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____981] in
                          uu____978 :: uu____979 in
                        let uu____982 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____974 uu____982 in
                      FStar_Syntax_Syntax.mk_Total uu____973 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____986 =
                      let uu____987 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____987 in
                    let uu____993 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____995 =
                        let uu____998 =
                          let uu____1004 =
                            let uu____1006 =
                              let uu____1009 =
                                let uu____1015 =
                                  let uu____1016 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1016 in
                                [uu____1015] in
                              FStar_Syntax_Util.mk_app l_ite uu____1009 in
                            [uu____1006] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1004 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____998 in
                      FStar_Syntax_Util.ascribe uu____995
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____986 uu____993
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1041 = mk_lid "wp_if_then_else" in
                    register env1 uu____1041 wp_if_then_else in
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
                      let uu____1052 =
                        let uu____1058 =
                          let uu____1060 =
                            let uu____1063 =
                              let uu____1069 =
                                let uu____1071 =
                                  let uu____1074 =
                                    let uu____1080 =
                                      let uu____1081 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1081 in
                                    [uu____1080] in
                                  FStar_Syntax_Util.mk_app l_and uu____1074 in
                                [uu____1071] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1069 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1063 in
                          let uu____1086 =
                            let uu____1090 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1090] in
                          uu____1060 :: uu____1086 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1058 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1052 in
                    let uu____1093 =
                      let uu____1094 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1094 in
                    FStar_Syntax_Util.abs uu____1093 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1101 = mk_lid "wp_assert" in
                    register env1 uu____1101 wp_assert in
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
                      let uu____1112 =
                        let uu____1118 =
                          let uu____1120 =
                            let uu____1123 =
                              let uu____1129 =
                                let uu____1131 =
                                  let uu____1134 =
                                    let uu____1140 =
                                      let uu____1141 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1141 in
                                    [uu____1140] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1134 in
                                [uu____1131] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1129 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1123 in
                          let uu____1146 =
                            let uu____1150 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1150] in
                          uu____1120 :: uu____1146 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1118 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1112 in
                    let uu____1153 =
                      let uu____1154 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1154 in
                    FStar_Syntax_Util.abs uu____1153 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1161 = mk_lid "wp_assume" in
                    register env1 uu____1161 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1170 =
                        let uu____1174 =
                          let uu____1175 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1175 in
                        [uu____1174] in
                      let uu____1176 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1170 uu____1176 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1183 =
                        let uu____1189 =
                          let uu____1191 =
                            let uu____1194 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1194 in
                          let uu____1200 =
                            let uu____1204 =
                              let uu____1207 =
                                let uu____1213 =
                                  let uu____1215 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1215] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1213 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1207 in
                            [uu____1204] in
                          uu____1191 :: uu____1200 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1189 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1183 in
                    let uu____1222 =
                      let uu____1223 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1223 in
                    FStar_Syntax_Util.abs uu____1222 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1230 = mk_lid "wp_close" in
                    register env1 uu____1230 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1241 =
                      let uu____1247 =
                        let uu____1248 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1248 in
                      FStar_Util.Inl uu____1247 in
                    Some uu____1241 in
                  let ret_gtot_type =
                    let uu____1268 =
                      let uu____1274 =
                        let uu____1275 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1275 in
                      FStar_Util.Inl uu____1274 in
                    Some uu____1268 in
                  let mk_forall1 x body =
                    let uu____1295 =
                      let uu____1298 =
                        let uu____1299 =
                          let uu____1309 =
                            let uu____1311 =
                              let uu____1312 =
                                let uu____1313 =
                                  let uu____1314 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1314] in
                                FStar_Syntax_Util.abs uu____1313 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1312 in
                            [uu____1311] in
                          (FStar_Syntax_Util.tforall, uu____1309) in
                        FStar_Syntax_Syntax.Tm_app uu____1299 in
                      FStar_Syntax_Syntax.mk uu____1298 in
                    uu____1295 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1328 =
                      let uu____1329 = FStar_Syntax_Subst.compress t in
                      uu____1329.FStar_Syntax_Syntax.n in
                    match uu____1328 with
                    | FStar_Syntax_Syntax.Tm_type uu____1332 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1347  ->
                              match uu____1347 with
                              | (b,uu____1351) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1352 -> true in
                  let rec is_monotonic t =
                    let uu____1357 =
                      let uu____1358 = FStar_Syntax_Subst.compress t in
                      uu____1358.FStar_Syntax_Syntax.n in
                    match uu____1357 with
                    | FStar_Syntax_Syntax.Tm_type uu____1361 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1376  ->
                              match uu____1376 with
                              | (b,uu____1380) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1381 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1433 =
                      let uu____1434 = FStar_Syntax_Subst.compress t1 in
                      uu____1434.FStar_Syntax_Syntax.n in
                    match uu____1433 with
                    | FStar_Syntax_Syntax.Tm_type uu____1437 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1440);
                                      FStar_Syntax_Syntax.tk = uu____1441;
                                      FStar_Syntax_Syntax.pos = uu____1442;
                                      FStar_Syntax_Syntax.vars = uu____1443;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1466 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1466
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1469 =
                              let uu____1472 =
                                let uu____1478 =
                                  let uu____1479 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1479 in
                                [uu____1478] in
                              FStar_Syntax_Util.mk_app x uu____1472 in
                            let uu____1480 =
                              let uu____1483 =
                                let uu____1489 =
                                  let uu____1490 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1490 in
                                [uu____1489] in
                              FStar_Syntax_Util.mk_app y uu____1483 in
                            mk_rel1 b uu____1469 uu____1480 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1497 =
                               let uu____1498 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1501 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1498 uu____1501 in
                             let uu____1504 =
                               let uu____1505 =
                                 let uu____1508 =
                                   let uu____1514 =
                                     let uu____1515 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1515 in
                                   [uu____1514] in
                                 FStar_Syntax_Util.mk_app x uu____1508 in
                               let uu____1516 =
                                 let uu____1519 =
                                   let uu____1525 =
                                     let uu____1526 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1526 in
                                   [uu____1525] in
                                 FStar_Syntax_Util.mk_app y uu____1519 in
                               mk_rel1 b uu____1505 uu____1516 in
                             FStar_Syntax_Util.mk_imp uu____1497 uu____1504 in
                           let uu____1527 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1527)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1530);
                                      FStar_Syntax_Syntax.tk = uu____1531;
                                      FStar_Syntax_Syntax.pos = uu____1532;
                                      FStar_Syntax_Syntax.vars = uu____1533;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1556 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1556
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1559 =
                              let uu____1562 =
                                let uu____1568 =
                                  let uu____1569 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1569 in
                                [uu____1568] in
                              FStar_Syntax_Util.mk_app x uu____1562 in
                            let uu____1570 =
                              let uu____1573 =
                                let uu____1579 =
                                  let uu____1580 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1580 in
                                [uu____1579] in
                              FStar_Syntax_Util.mk_app y uu____1573 in
                            mk_rel1 b uu____1559 uu____1570 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1587 =
                               let uu____1588 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1591 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1588 uu____1591 in
                             let uu____1594 =
                               let uu____1595 =
                                 let uu____1598 =
                                   let uu____1604 =
                                     let uu____1605 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1605 in
                                   [uu____1604] in
                                 FStar_Syntax_Util.mk_app x uu____1598 in
                               let uu____1606 =
                                 let uu____1609 =
                                   let uu____1615 =
                                     let uu____1616 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1616 in
                                   [uu____1615] in
                                 FStar_Syntax_Util.mk_app y uu____1609 in
                               mk_rel1 b uu____1595 uu____1606 in
                             FStar_Syntax_Util.mk_imp uu____1587 uu____1594 in
                           let uu____1617 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1617)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___102_1638 = t1 in
                          let uu____1639 =
                            let uu____1640 =
                              let uu____1648 =
                                let uu____1649 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1649 in
                              ([binder], uu____1648) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1640 in
                          {
                            FStar_Syntax_Syntax.n = uu____1639;
                            FStar_Syntax_Syntax.tk =
                              (uu___102_1638.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___102_1638.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___102_1638.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1661 ->
                        failwith "unhandled arrow"
                    | uu____1669 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1686 =
                        let uu____1687 = FStar_Syntax_Subst.compress t1 in
                        uu____1687.FStar_Syntax_Syntax.n in
                      match uu____1686 with
                      | FStar_Syntax_Syntax.Tm_type uu____1692 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1709 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1709
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1724 =
                                let uu____1725 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1725 i in
                              FStar_Syntax_Syntax.fvar uu____1724
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1746 =
                            let uu____1754 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1763  ->
                                     match uu____1763 with
                                     | (t2,q) ->
                                         let uu____1770 = project i x in
                                         let uu____1771 = project i y in
                                         mk_stronger t2 uu____1770 uu____1771)
                                args in
                            match uu____1754 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1746 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1818);
                                      FStar_Syntax_Syntax.tk = uu____1819;
                                      FStar_Syntax_Syntax.pos = uu____1820;
                                      FStar_Syntax_Syntax.vars = uu____1821;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1843  ->
                                   match uu____1843 with
                                   | (bv,q) ->
                                       let uu____1848 =
                                         let uu____1849 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1849 in
                                       FStar_Syntax_Syntax.gen_bv uu____1848
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1853 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1853) bvs in
                          let body =
                            let uu____1857 = FStar_Syntax_Util.mk_app x args in
                            let uu____1858 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1857 uu____1858 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1863);
                                      FStar_Syntax_Syntax.tk = uu____1864;
                                      FStar_Syntax_Syntax.pos = uu____1865;
                                      FStar_Syntax_Syntax.vars = uu____1866;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1888  ->
                                   match uu____1888 with
                                   | (bv,q) ->
                                       let uu____1893 =
                                         let uu____1894 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1894 in
                                       FStar_Syntax_Syntax.gen_bv uu____1893
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1898 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1898) bvs in
                          let body =
                            let uu____1902 = FStar_Syntax_Util.mk_app x args in
                            let uu____1903 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1902 uu____1903 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1906 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1912 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1913 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1914 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1912 uu____1913 uu____1914 in
                    let uu____1915 =
                      let uu____1916 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1916 in
                    FStar_Syntax_Util.abs uu____1915 body ret_tot_type in
                  let stronger1 =
                    let uu____1931 = mk_lid "stronger" in
                    register env1 uu____1931 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1937 = FStar_Util.prefix gamma in
                    match uu____1937 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1963 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1963 in
                          let uu____1966 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1966 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1974 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1974 in
                              let guard_free1 =
                                let uu____1981 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1981 in
                              let pat =
                                let uu____1985 =
                                  let uu____1991 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1991] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1985 in
                              let pattern_guarded_body =
                                let uu____1995 =
                                  let uu____1996 =
                                    let uu____2001 =
                                      let uu____2002 =
                                        let uu____2009 =
                                          let uu____2011 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2011] in
                                        [uu____2009] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2002 in
                                    (body, uu____2001) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1996 in
                                mk1 uu____1995 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2014 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2017 =
                            let uu____2018 =
                              let uu____2019 =
                                let uu____2020 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2023 =
                                  let uu____2029 = args_of_binders1 wp_args in
                                  let uu____2031 =
                                    let uu____2033 =
                                      let uu____2034 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2034 in
                                    [uu____2033] in
                                  FStar_List.append uu____2029 uu____2031 in
                                FStar_Syntax_Util.mk_app uu____2020
                                  uu____2023 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2019 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2018 in
                          FStar_Syntax_Util.abs gamma uu____2017
                            ret_gtot_type in
                        let uu____2035 =
                          let uu____2036 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2036 in
                        FStar_Syntax_Util.abs uu____2035 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2043 = mk_lid "wp_ite" in
                    register env1 uu____2043 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2049 = FStar_Util.prefix gamma in
                    match uu____2049 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2073 =
                            let uu____2074 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2077 =
                              let uu____2083 =
                                let uu____2084 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2084 in
                              [uu____2083] in
                            FStar_Syntax_Util.mk_app uu____2074 uu____2077 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2073 in
                        let uu____2085 =
                          let uu____2086 =
                            let uu____2090 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2090 gamma in
                          FStar_List.append binders uu____2086 in
                        FStar_Syntax_Util.abs uu____2085 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2099 = mk_lid "null_wp" in
                    register env1 uu____2099 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2108 =
                        let uu____2114 =
                          let uu____2116 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2117 =
                            let uu____2119 =
                              let uu____2122 =
                                let uu____2128 =
                                  let uu____2129 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2129 in
                                [uu____2128] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2122 in
                            let uu____2130 =
                              let uu____2134 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2134] in
                            uu____2119 :: uu____2130 in
                          uu____2116 :: uu____2117 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2114 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2108 in
                    let uu____2137 =
                      let uu____2138 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2138 in
                    FStar_Syntax_Util.abs uu____2137 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2145 = mk_lid "wp_trivial" in
                    register env1 uu____2145 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2150 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2150
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2155 =
                      let uu____2157 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2157 in
                    let uu____2162 =
                      let uu___103_2163 = ed in
                      let uu____2164 =
                        let uu____2165 = c wp_if_then_else2 in
                        ([], uu____2165) in
                      let uu____2167 =
                        let uu____2168 = c wp_ite2 in ([], uu____2168) in
                      let uu____2170 =
                        let uu____2171 = c stronger2 in ([], uu____2171) in
                      let uu____2173 =
                        let uu____2174 = c wp_close2 in ([], uu____2174) in
                      let uu____2176 =
                        let uu____2177 = c wp_assert2 in ([], uu____2177) in
                      let uu____2179 =
                        let uu____2180 = c wp_assume2 in ([], uu____2180) in
                      let uu____2182 =
                        let uu____2183 = c null_wp2 in ([], uu____2183) in
                      let uu____2185 =
                        let uu____2186 = c wp_trivial2 in ([], uu____2186) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_2163.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_2163.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_2163.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_2163.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_2163.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_2163.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_2163.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2164;
                        FStar_Syntax_Syntax.ite_wp = uu____2167;
                        FStar_Syntax_Syntax.stronger = uu____2170;
                        FStar_Syntax_Syntax.close_wp = uu____2173;
                        FStar_Syntax_Syntax.assert_p = uu____2176;
                        FStar_Syntax_Syntax.assume_p = uu____2179;
                        FStar_Syntax_Syntax.null_wp = uu____2182;
                        FStar_Syntax_Syntax.trivial = uu____2185;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_2163.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_2163.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_2163.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_2163.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2155, uu____2162)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_2198 = dmff_env in
      {
        env = env';
        subst = (uu___104_2198.subst);
        tc_const = (uu___104_2198.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2211 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2223 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___90_2233  ->
    match uu___90_2233 with
    | FStar_Syntax_Syntax.Total (t,uu____2235) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___89_2244  ->
                match uu___89_2244 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2245 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2247 =
          let uu____2248 =
            let uu____2249 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2249 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2248 in
        failwith uu____2247
    | FStar_Syntax_Syntax.GTotal uu____2250 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___91_2258  ->
    match uu___91_2258 with
    | N t ->
        let uu____2260 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2260
    | M t ->
        let uu____2262 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2262
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2266,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2268;
                      FStar_Syntax_Syntax.pos = uu____2269;
                      FStar_Syntax_Syntax.vars = uu____2270;_})
        -> nm_of_comp n2
    | uu____2281 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2293 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2293 with | M uu____2294 -> true | N uu____2295 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2299 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2309 =
        let uu____2313 =
          let uu____2314 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2314 in
        [uu____2313] in
      let uu____2315 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2309 uu____2315 in
    let uu____2318 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2318
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
          (let uu____2353 =
             let uu____2361 =
               let uu____2365 =
                 let uu____2368 =
                   let uu____2369 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2369 in
                 let uu____2370 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2368, uu____2370) in
               [uu____2365] in
             let uu____2375 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2361, uu____2375) in
           FStar_Syntax_Syntax.Tm_arrow uu____2353)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2404) ->
          let binders1 =
            FStar_List.map
              (fun uu____2423  ->
                 match uu____2423 with
                 | (bv,aqual) ->
                     let uu____2430 =
                       let uu___105_2431 = bv in
                       let uu____2432 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_2431.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_2431.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2432
                       } in
                     (uu____2430, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2435,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2437);
                             FStar_Syntax_Syntax.tk = uu____2438;
                             FStar_Syntax_Syntax.pos = uu____2439;
                             FStar_Syntax_Syntax.vars = uu____2440;_})
               ->
               let uu____2457 =
                 let uu____2458 =
                   let uu____2466 =
                     let uu____2467 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2467 in
                   (binders1, uu____2466) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2458 in
               mk1 uu____2457
           | uu____2471 ->
               let uu____2472 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2472 with
                | N hn ->
                    let uu____2474 =
                      let uu____2475 =
                        let uu____2483 =
                          let uu____2484 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2484 in
                        (binders1, uu____2483) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2475 in
                    mk1 uu____2474
                | M a ->
                    let uu____2489 =
                      let uu____2490 =
                        let uu____2498 =
                          let uu____2502 =
                            let uu____2506 =
                              let uu____2509 =
                                let uu____2510 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2510 in
                              let uu____2511 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2509, uu____2511) in
                            [uu____2506] in
                          FStar_List.append binders1 uu____2502 in
                        let uu____2518 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2498, uu____2518) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2490 in
                    mk1 uu____2489))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2569 = f x in
                    FStar_Util.string_builder_append strb uu____2569);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2573 = f x1 in
                         FStar_Util.string_builder_append strb uu____2573))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2575 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2576 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2575 uu____2576 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2584 =
              let uu____2585 = FStar_Syntax_Subst.compress ty in
              uu____2585.FStar_Syntax_Syntax.n in
            match uu____2584 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2600 =
                  let uu____2601 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2601 in
                if uu____2600
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2615 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2615 s in
                       let uu____2617 =
                         let uu____2618 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2618 in
                       if uu____2617
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2621 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2621 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2632  ->
                                  match uu____2632 with
                                  | (bv,uu____2638) ->
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
            | uu____2651 ->
                ((let uu____2653 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2653);
                 false) in
          let rec is_valid_application head2 =
            let uu____2658 =
              let uu____2659 = FStar_Syntax_Subst.compress head2 in
              uu____2659.FStar_Syntax_Syntax.n in
            match uu____2658 with
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
                  (let uu____2663 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2663)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2676 -> true
                 | uu____2686 ->
                     ((let uu____2688 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2688);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2689 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2690 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2692) ->
                is_valid_application t2
            | uu____2697 -> false in
          let uu____2698 = is_valid_application head1 in
          if uu____2698
          then
            let uu____2699 =
              let uu____2700 =
                let uu____2710 =
                  FStar_List.map
                    (fun uu____2720  ->
                       match uu____2720 with
                       | (t2,qual) ->
                           let uu____2733 = star_type' env t2 in
                           (uu____2733, qual)) args in
                (head1, uu____2710) in
              FStar_Syntax_Syntax.Tm_app uu____2700 in
            mk1 uu____2699
          else
            (let uu____2740 =
               let uu____2741 =
                 let uu____2742 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2742 in
               FStar_Errors.Err uu____2741 in
             raise uu____2740)
      | FStar_Syntax_Syntax.Tm_bvar uu____2743 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2744 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2745 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2746 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2772 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2772 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___108_2778 = env in
                 let uu____2779 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2779;
                   subst = (uu___108_2778.subst);
                   tc_const = (uu___108_2778.tc_const)
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
               ((let uu___109_2796 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_2796.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_2796.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2803 =
            let uu____2804 =
              let uu____2809 = star_type' env t2 in (uu____2809, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2804 in
          mk1 uu____2803
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2847 =
            let uu____2848 =
              let uu____2866 = star_type' env e in
              let uu____2867 =
                let uu____2877 =
                  let uu____2882 = star_type' env t2 in
                  FStar_Util.Inl uu____2882 in
                (uu____2877, None) in
              (uu____2866, uu____2867, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2848 in
          mk1 uu____2847
      | FStar_Syntax_Syntax.Tm_ascribed uu____2904 ->
          let uu____2922 =
            let uu____2923 =
              let uu____2924 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2924 in
            FStar_Errors.Err uu____2923 in
          raise uu____2922
      | FStar_Syntax_Syntax.Tm_refine uu____2925 ->
          let uu____2930 =
            let uu____2931 =
              let uu____2932 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2932 in
            FStar_Errors.Err uu____2931 in
          raise uu____2930
      | FStar_Syntax_Syntax.Tm_uinst uu____2933 ->
          let uu____2938 =
            let uu____2939 =
              let uu____2940 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2940 in
            FStar_Errors.Err uu____2939 in
          raise uu____2938
      | FStar_Syntax_Syntax.Tm_constant uu____2941 ->
          let uu____2942 =
            let uu____2943 =
              let uu____2944 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2944 in
            FStar_Errors.Err uu____2943 in
          raise uu____2942
      | FStar_Syntax_Syntax.Tm_match uu____2945 ->
          let uu____2961 =
            let uu____2962 =
              let uu____2963 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2963 in
            FStar_Errors.Err uu____2962 in
          raise uu____2961
      | FStar_Syntax_Syntax.Tm_let uu____2964 ->
          let uu____2972 =
            let uu____2973 =
              let uu____2974 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2974 in
            FStar_Errors.Err uu____2973 in
          raise uu____2972
      | FStar_Syntax_Syntax.Tm_uvar uu____2975 ->
          let uu____2984 =
            let uu____2985 =
              let uu____2986 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2986 in
            FStar_Errors.Err uu____2985 in
          raise uu____2984
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2987 =
            let uu____2988 =
              let uu____2989 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2989 in
            FStar_Errors.Err uu____2988 in
          raise uu____2987
      | FStar_Syntax_Syntax.Tm_delayed uu____2990 -> failwith "impossible"
let is_monadic uu___93_3023 =
  match uu___93_3023 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3035;
        FStar_Syntax_Syntax.res_typ = uu____3036;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3038;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3055  ->
              match uu___92_3055 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3056 -> false))
  | Some (FStar_Util.Inr (uu____3057,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3070  ->
              match uu___92_3070 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3071 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3075 =
      let uu____3076 = FStar_Syntax_Subst.compress t in
      uu____3076.FStar_Syntax_Syntax.n in
    match uu____3075 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3096 =
            let uu____3097 = FStar_List.hd args in fst uu____3097 in
          is_C uu____3096 in
        if r
        then
          ((let uu____3109 =
              let uu____3110 =
                FStar_List.for_all
                  (fun uu____3113  ->
                     match uu____3113 with | (h,uu____3117) -> is_C h) args in
              Prims.op_Negation uu____3110 in
            if uu____3109 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3121 =
              let uu____3122 =
                FStar_List.for_all
                  (fun uu____3125  ->
                     match uu____3125 with
                     | (h,uu____3129) ->
                         let uu____3130 = is_C h in
                         Prims.op_Negation uu____3130) args in
              Prims.op_Negation uu____3122 in
            if uu____3121 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3144 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3144 with
         | M t1 ->
             ((let uu____3147 = is_C t1 in
               if uu____3147 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3151) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3157) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3163,uu____3164) -> is_C t1
    | uu____3193 -> false
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
          let uu____3220 =
            let uu____3221 =
              let uu____3231 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3232 =
                let uu____3236 =
                  let uu____3239 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3239) in
                [uu____3236] in
              (uu____3231, uu____3232) in
            FStar_Syntax_Syntax.Tm_app uu____3221 in
          mk1 uu____3220 in
        let uu____3247 =
          let uu____3248 = FStar_Syntax_Syntax.mk_binder p in [uu____3248] in
        let uu____3249 =
          let uu____3256 =
            let uu____3262 =
              let uu____3263 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3263 in
            FStar_Util.Inl uu____3262 in
          Some uu____3256 in
        FStar_Syntax_Util.abs uu____3247 body uu____3249
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___94_3276  ->
    match uu___94_3276 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3277 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
        let return_if uu____3421 =
          match uu____3421 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3442 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3443 =
                       let uu____3444 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3444 in
                     Prims.op_Negation uu____3443) in
                if uu____3442
                then
                  let uu____3445 =
                    let uu____3446 =
                      let uu____3447 = FStar_Syntax_Print.term_to_string e in
                      let uu____3448 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3449 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3447 uu____3448 uu____3449 in
                    FStar_Errors.Err uu____3446 in
                  raise uu____3445
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3463 = mk_return env t1 s_e in
                     ((M t1), uu____3463, u_e)))
               | (M t1,N t2) ->
                   let uu____3466 =
                     let uu____3467 =
                       let uu____3468 = FStar_Syntax_Print.term_to_string e in
                       let uu____3469 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3470 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3468 uu____3469 uu____3470 in
                     FStar_Errors.Err uu____3467 in
                   raise uu____3466) in
        let ensure_m env1 e2 =
          let strip_m uu___95_3496 =
            match uu___95_3496 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3506 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3517 =
                let uu____3518 =
                  let uu____3521 =
                    let uu____3522 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3522 in
                  (uu____3521, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3518 in
              raise uu____3517
          | M uu____3526 ->
              let uu____3527 = check env1 e2 context_nm in strip_m uu____3527 in
        let uu____3531 =
          let uu____3532 = FStar_Syntax_Subst.compress e in
          uu____3532.FStar_Syntax_Syntax.n in
        match uu____3531 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3538 ->
            let uu____3539 = infer env e in return_if uu____3539
        | FStar_Syntax_Syntax.Tm_name uu____3543 ->
            let uu____3544 = infer env e in return_if uu____3544
        | FStar_Syntax_Syntax.Tm_fvar uu____3548 ->
            let uu____3549 = infer env e in return_if uu____3549
        | FStar_Syntax_Syntax.Tm_abs uu____3553 ->
            let uu____3568 = infer env e in return_if uu____3568
        | FStar_Syntax_Syntax.Tm_constant uu____3572 ->
            let uu____3573 = infer env e in return_if uu____3573
        | FStar_Syntax_Syntax.Tm_app uu____3577 ->
            let uu____3587 = infer env e in return_if uu____3587
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3634) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3640) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3646,uu____3647) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3676 ->
            let uu____3684 =
              let uu____3685 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3685 in
            failwith uu____3684
        | FStar_Syntax_Syntax.Tm_type uu____3689 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3693 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3704 ->
            let uu____3709 =
              let uu____3710 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3710 in
            failwith uu____3709
        | FStar_Syntax_Syntax.Tm_uvar uu____3714 ->
            let uu____3723 =
              let uu____3724 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3724 in
            failwith uu____3723
        | FStar_Syntax_Syntax.Tm_delayed uu____3728 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3752 =
              let uu____3753 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3753 in
            failwith uu____3752
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
      let uu____3775 =
        let uu____3776 = FStar_Syntax_Subst.compress e in
        uu____3776.FStar_Syntax_Syntax.n in
      match uu____3775 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___110_3816 = env in
            let uu____3817 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3817;
              subst = (uu___110_3816.subst);
              tc_const = (uu___110_3816.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3826  ->
                 match uu____3826 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___111_3834 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___111_3834.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___111_3834.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3835 =
            FStar_List.fold_left
              (fun uu____3844  ->
                 fun uu____3845  ->
                   match (uu____3844, uu____3845) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3873 = is_C c in
                       if uu____3873
                       then
                         let xw =
                           let uu____3878 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3878 in
                         let x =
                           let uu___112_3880 = bv in
                           let uu____3881 =
                             let uu____3884 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3884 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___112_3880.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___112_3880.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3881
                           } in
                         let env3 =
                           let uu___113_3886 = env2 in
                           let uu____3887 =
                             let uu____3889 =
                               let uu____3890 =
                                 let uu____3895 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3895) in
                               FStar_Syntax_Syntax.NT uu____3890 in
                             uu____3889 :: (env2.subst) in
                           {
                             env = (uu___113_3886.env);
                             subst = uu____3887;
                             tc_const = (uu___113_3886.tc_const)
                           } in
                         let uu____3896 =
                           let uu____3898 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3899 =
                             let uu____3901 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3901 :: acc in
                           uu____3898 :: uu____3899 in
                         (env3, uu____3896)
                       else
                         (let x =
                            let uu___114_3905 = bv in
                            let uu____3906 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_3905.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_3905.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3906
                            } in
                          let uu____3909 =
                            let uu____3911 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3911 :: acc in
                          (env2, uu____3909))) (env1, []) binders1 in
          (match uu____3835 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3923 =
                 let check_what =
                   let uu____3935 = is_monadic what in
                   if uu____3935 then check_m else check_n in
                 let uu____3944 = check_what env2 body1 in
                 match uu____3944 with
                 | (t,s_body,u_body) ->
                     let uu____3954 =
                       let uu____3955 =
                         let uu____3956 = is_monadic what in
                         if uu____3956 then M t else N t in
                       comp_of_nm uu____3955 in
                     (uu____3954, s_body, u_body) in
               (match uu____3923 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3999 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___96_4001  ->
                                    match uu___96_4001 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____4002 -> false)) in
                          if uu____3999
                          then
                            let double_starred_comp =
                              let uu____4010 =
                                let uu____4011 =
                                  let uu____4012 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____4012 in
                                FStar_All.pipe_left double_star uu____4011 in
                              FStar_Syntax_Syntax.mk_Total uu____4010 in
                            let flags =
                              FStar_List.filter
                                (fun uu___97_4017  ->
                                   match uu___97_4017 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____4018 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____4019 =
                              let uu____4025 =
                                let uu____4026 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____4026 in
                              FStar_Util.Inl uu____4025 in
                            Some uu____4019
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___115_4046 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___115_4046.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___115_4046.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___115_4046.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4047  ->
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
                          let uu____4064 =
                            let uu____4070 =
                              let uu____4074 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___98_4076  ->
                                        match uu___98_4076 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4077 -> false)) in
                              if uu____4074
                              then
                                let uu____4081 =
                                  FStar_List.filter
                                    (fun uu___99_4083  ->
                                       match uu___99_4083 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4084 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4081)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4070 in
                          Some uu____4064 in
                    let uu____4096 =
                      let comp1 =
                        let uu____4108 = is_monadic what in
                        let uu____4109 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4108 uu____4109 in
                      let uu____4110 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4110,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4096 with
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
                FStar_Syntax_Syntax.ty = uu____4188;
                FStar_Syntax_Syntax.p = uu____4189;_};
            FStar_Syntax_Syntax.fv_delta = uu____4190;
            FStar_Syntax_Syntax.fv_qual = uu____4191;_}
          ->
          let uu____4197 =
            let uu____4200 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4200 in
          (match uu____4197 with
           | (uu____4216,t) ->
               let uu____4218 = let uu____4219 = normalize1 t in N uu____4219 in
               (uu____4218, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4236 = check_n env head1 in
          (match uu____4236 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4250 =
                   let uu____4251 = FStar_Syntax_Subst.compress t in
                   uu____4251.FStar_Syntax_Syntax.n in
                 match uu____4250 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4254 -> true
                 | uu____4262 -> false in
               let rec flatten1 t =
                 let uu____4274 =
                   let uu____4275 = FStar_Syntax_Subst.compress t in
                   uu____4275.FStar_Syntax_Syntax.n in
                 match uu____4274 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4287);
                                FStar_Syntax_Syntax.tk = uu____4288;
                                FStar_Syntax_Syntax.pos = uu____4289;
                                FStar_Syntax_Syntax.vars = uu____4290;_})
                     when is_arrow t1 ->
                     let uu____4307 = flatten1 t1 in
                     (match uu____4307 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4359,uu____4360)
                     -> flatten1 e1
                 | uu____4389 ->
                     let uu____4390 =
                       let uu____4391 =
                         let uu____4392 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4392 in
                       FStar_Errors.Err uu____4391 in
                     raise uu____4390 in
               let uu____4400 = flatten1 t_head in
               (match uu____4400 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4445 =
                          let uu____4446 =
                            let uu____4447 = FStar_Util.string_of_int n1 in
                            let uu____4451 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4457 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4447 uu____4451 uu____4457 in
                          FStar_Errors.Err uu____4446 in
                        raise uu____4445)
                     else ();
                     (let uu____4462 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4462 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4489 args1 =
                            match uu____4489 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4532 =
                                       let uu____4533 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4533.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4532
                                 | (binders3,[]) ->
                                     let uu____4552 =
                                       let uu____4553 =
                                         let uu____4556 =
                                           let uu____4557 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4557 in
                                         FStar_Syntax_Subst.compress
                                           uu____4556 in
                                       uu____4553.FStar_Syntax_Syntax.n in
                                     (match uu____4552 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4573 =
                                            let uu____4574 =
                                              let uu____4575 =
                                                let uu____4583 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4583) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4575 in
                                            mk1 uu____4574 in
                                          N uu____4573
                                      | uu____4587 -> failwith "wat?")
                                 | ([],uu____4588::uu____4589) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4614)::binders3,(arg,uu____4617)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4651 = FStar_List.splitAt n' binders1 in
                          (match uu____4651 with
                           | (binders2,uu____4668) ->
                               let uu____4681 =
                                 let uu____4691 =
                                   FStar_List.map2
                                     (fun uu____4711  ->
                                        fun uu____4712  ->
                                          match (uu____4711, uu____4712) with
                                          | ((bv,uu____4729),(arg,q)) ->
                                              let uu____4736 =
                                                let uu____4737 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4737.FStar_Syntax_Syntax.n in
                                              (match uu____4736 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4747 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4760 ->
                                                   let uu____4761 =
                                                     check_n env arg in
                                                   (match uu____4761 with
                                                    | (uu____4772,s_arg,u_arg)
                                                        ->
                                                        let uu____4775 =
                                                          let uu____4779 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4779
                                                          then
                                                            let uu____4783 =
                                                              let uu____4786
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4786, q) in
                                                            [uu____4783;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4775))))
                                     binders2 args in
                                 FStar_List.split uu____4691 in
                               (match uu____4681 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4833 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4839 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4833, uu____4839)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4888) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4894) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4900,uu____4901) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4931 = let uu____4932 = env.tc_const c in N uu____4932 in
          (uu____4931, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4933 ->
          let uu____4941 =
            let uu____4942 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4942 in
          failwith uu____4941
      | FStar_Syntax_Syntax.Tm_type uu____4946 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4950 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4961 ->
          let uu____4966 =
            let uu____4967 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4967 in
          failwith uu____4966
      | FStar_Syntax_Syntax.Tm_uvar uu____4971 ->
          let uu____4980 =
            let uu____4981 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4981 in
          failwith uu____4980
      | FStar_Syntax_Syntax.Tm_delayed uu____4985 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5009 =
            let uu____5010 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____5010 in
          failwith uu____5009
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
          let uu____5048 = check_n env e0 in
          match uu____5048 with
          | (uu____5055,s_e0,u_e0) ->
              let uu____5058 =
                let uu____5076 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5109 = FStar_Syntax_Subst.open_branch b in
                       match uu____5109 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___116_5141 = env in
                             let uu____5142 =
                               let uu____5143 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5143 in
                             {
                               env = uu____5142;
                               subst = (uu___116_5141.subst);
                               tc_const = (uu___116_5141.tc_const)
                             } in
                           let uu____5145 = f env1 body in
                           (match uu____5145 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5194 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5076 in
              (match uu____5058 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5259 = FStar_List.hd nms in
                     match uu____5259 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_5263  ->
                          match uu___100_5263 with
                          | M uu____5264 -> true
                          | uu____5265 -> false) nms in
                   let uu____5266 =
                     let uu____5289 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5341  ->
                              match uu____5341 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5464 =
                                         check env original_body (M t2) in
                                       (match uu____5464 with
                                        | (uu____5487,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5516,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5289 in
                   (match uu____5266 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5635  ->
                                 match uu____5635 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5676 =
                                         let uu____5677 =
                                           let uu____5687 =
                                             let uu____5691 =
                                               let uu____5694 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5695 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5694, uu____5695) in
                                             [uu____5691] in
                                           (s_body, uu____5687) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5677 in
                                       mk1 uu____5676 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5717 =
                              let uu____5718 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5718] in
                            let uu____5719 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5721 =
                              let uu____5728 =
                                let uu____5734 =
                                  let uu____5735 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5735 in
                                FStar_Util.Inl uu____5734 in
                              Some uu____5728 in
                            FStar_Syntax_Util.abs uu____5717 uu____5719
                              uu____5721 in
                          let t1_star =
                            let uu____5749 =
                              let uu____5753 =
                                let uu____5754 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5754 in
                              [uu____5753] in
                            let uu____5755 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5749 uu____5755 in
                          let uu____5758 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5788 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5758, uu____5788)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5802 =
                             let uu____5805 =
                               let uu____5806 =
                                 let uu____5824 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5824,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5806 in
                             mk1 uu____5805 in
                           let uu____5851 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5802, uu____5851))))
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
              let uu____5894 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5894] in
            let uu____5895 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5895 with
            | (x_binders1,e21) ->
                let uu____5903 = infer env e1 in
                (match uu____5903 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5914 = is_C t1 in
                       if uu____5914
                       then
                         let uu___117_5915 = binding in
                         let uu____5916 =
                           let uu____5919 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5919 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___117_5915.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___117_5915.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5916;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___117_5915.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___117_5915.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___118_5922 = env in
                       let uu____5923 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5924 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5924.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5924.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5923;
                         subst = (uu___118_5922.subst);
                         tc_const = (uu___118_5922.tc_const)
                       } in
                     let uu____5925 = proceed env1 e21 in
                     (match uu____5925 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___120_5936 = binding in
                            let uu____5937 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_5936.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___120_5936.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5937;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_5936.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___120_5936.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5940 =
                            let uu____5943 =
                              let uu____5944 =
                                let uu____5952 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___121_5957 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5957.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5957.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5957.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5957.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5952) in
                              FStar_Syntax_Syntax.Tm_let uu____5944 in
                            mk1 uu____5943 in
                          let uu____5958 =
                            let uu____5961 =
                              let uu____5962 =
                                let uu____5970 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___122_5975 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_5975.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_5975.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_5975.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_5975.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5970) in
                              FStar_Syntax_Syntax.Tm_let uu____5962 in
                            mk1 uu____5961 in
                          (nm_rec, uu____5940, uu____5958))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___123_5984 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___123_5984.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___123_5984.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___123_5984.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___124_5986 = env in
                       let uu____5987 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_5988 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_5988.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_5988.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5987;
                         subst = (uu___124_5986.subst);
                         tc_const = (uu___124_5986.tc_const)
                       } in
                     let uu____5989 = ensure_m env1 e21 in
                     (match uu____5989 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____6006 =
                              let uu____6007 =
                                let uu____6017 =
                                  let uu____6021 =
                                    let uu____6024 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6025 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6024, uu____6025) in
                                  [uu____6021] in
                                (s_e2, uu____6017) in
                              FStar_Syntax_Syntax.Tm_app uu____6007 in
                            mk1 uu____6006 in
                          let s_e22 =
                            let uu____6034 =
                              let uu____6041 =
                                let uu____6047 =
                                  let uu____6048 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6048 in
                                FStar_Util.Inl uu____6047 in
                              Some uu____6041 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6034 in
                          let body =
                            let uu____6062 =
                              let uu____6063 =
                                let uu____6073 =
                                  let uu____6077 =
                                    let uu____6080 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6080) in
                                  [uu____6077] in
                                (s_e1, uu____6073) in
                              FStar_Syntax_Syntax.Tm_app uu____6063 in
                            mk1 uu____6062 in
                          let uu____6088 =
                            let uu____6089 =
                              let uu____6090 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6090] in
                            let uu____6091 =
                              let uu____6098 =
                                let uu____6104 =
                                  let uu____6105 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6105 in
                                FStar_Util.Inl uu____6104 in
                              Some uu____6098 in
                            FStar_Syntax_Util.abs uu____6089 body uu____6091 in
                          let uu____6116 =
                            let uu____6119 =
                              let uu____6120 =
                                let uu____6128 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___126_6133 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_6133.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_6133.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_6133.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_6133.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6128) in
                              FStar_Syntax_Syntax.Tm_let uu____6120 in
                            mk1 uu____6119 in
                          ((M t2), uu____6088, uu____6116)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6142 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6142 in
      let uu____6147 = check env e mn in
      match uu____6147 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6157 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6170 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6170 in
      let uu____6175 = check env e mn in
      match uu____6175 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6185 -> failwith "[check_m]: impossible"
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
        (let uu____6207 =
           let uu____6208 = is_C c in Prims.op_Negation uu____6208 in
         if uu____6207 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6220 =
           let uu____6221 = FStar_Syntax_Subst.compress c in
           uu____6221.FStar_Syntax_Syntax.n in
         match uu____6220 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6240 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6240 with
              | (wp_head,wp_args) ->
                  ((let uu____6267 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6280 =
                           let uu____6281 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6281 in
                         Prims.op_Negation uu____6280) in
                    if uu____6267 then failwith "mismatch" else ());
                   (let uu____6290 =
                      let uu____6291 =
                        let uu____6301 =
                          FStar_List.map2
                            (fun uu____6311  ->
                               fun uu____6312  ->
                                 match (uu____6311, uu____6312) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6335 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6335
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6338 = print_implicit q in
                                         let uu____6339 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6338 uu____6339)
                                      else ();
                                      (let uu____6341 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6341, q)))) args wp_args in
                        (head1, uu____6301) in
                      FStar_Syntax_Syntax.Tm_app uu____6291 in
                    mk1 uu____6290)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6363 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6363 with
              | (binders_orig,comp1) ->
                  let uu____6368 =
                    let uu____6376 =
                      FStar_List.map
                        (fun uu____6390  ->
                           match uu____6390 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6403 = is_C h in
                               if uu____6403
                               then
                                 let w' =
                                   let uu____6410 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6410 in
                                 let uu____6411 =
                                   let uu____6415 =
                                     let uu____6419 =
                                       let uu____6422 =
                                         let uu____6423 =
                                           let uu____6424 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6424 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6423 in
                                       (uu____6422, q) in
                                     [uu____6419] in
                                   (w', q) :: uu____6415 in
                                 (w', uu____6411)
                               else
                                 (let x =
                                    let uu____6436 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6436 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6376 in
                  (match uu____6368 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6466 =
                           let uu____6468 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6468 in
                         FStar_Syntax_Subst.subst_comp uu____6466 comp1 in
                       let app =
                         let uu____6472 =
                           let uu____6473 =
                             let uu____6483 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6490 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6491 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6490, uu____6491)) bvs in
                             (wp, uu____6483) in
                           FStar_Syntax_Syntax.Tm_app uu____6473 in
                         mk1 uu____6472 in
                       let comp3 =
                         let uu____6496 = type_of_comp comp2 in
                         let uu____6497 = is_monadic_comp comp2 in
                         trans_G env uu____6496 uu____6497 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6499,uu____6500) ->
             trans_F_ env e wp
         | uu____6529 -> failwith "impossible trans_F_")
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
            let uu____6544 =
              let uu____6545 = star_type' env h in
              let uu____6548 =
                let uu____6554 =
                  let uu____6557 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6557) in
                [uu____6554] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6545;
                FStar_Syntax_Syntax.effect_args = uu____6548;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6544
          else
            (let uu____6563 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6563)
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
    fun t  -> let uu____6574 = n env.env t in star_type' env uu____6574
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6586 = n env.env t in check_n env uu____6586
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6596 = n env.env c in
        let uu____6597 = n env.env wp in trans_F_ env uu____6596 uu____6597