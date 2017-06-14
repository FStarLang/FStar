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
              let uu___100_68 = a in
              let uu____69 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___100_68.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___100_68.FStar_Syntax_Syntax.index);
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
                             let uu____1495 =
                               let uu____1496 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1499 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1496 uu____1499 in
                             let uu____1502 =
                               let uu____1503 =
                                 let uu____1506 =
                                   let uu____1512 =
                                     let uu____1513 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1513 in
                                   [uu____1512] in
                                 FStar_Syntax_Util.mk_app x uu____1506 in
                               let uu____1514 =
                                 let uu____1517 =
                                   let uu____1523 =
                                     let uu____1524 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1524 in
                                   [uu____1523] in
                                 FStar_Syntax_Util.mk_app y uu____1517 in
                               mk_rel1 b uu____1503 uu____1514 in
                             FStar_Syntax_Util.mk_imp uu____1495 uu____1502 in
                           let uu____1525 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1525)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1528);
                                      FStar_Syntax_Syntax.tk = uu____1529;
                                      FStar_Syntax_Syntax.pos = uu____1530;
                                      FStar_Syntax_Syntax.vars = uu____1531;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1554 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1554
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1557 =
                              let uu____1560 =
                                let uu____1566 =
                                  let uu____1567 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1567 in
                                [uu____1566] in
                              FStar_Syntax_Util.mk_app x uu____1560 in
                            let uu____1568 =
                              let uu____1571 =
                                let uu____1577 =
                                  let uu____1578 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1578 in
                                [uu____1577] in
                              FStar_Syntax_Util.mk_app y uu____1571 in
                            mk_rel1 b uu____1557 uu____1568 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1583 =
                               let uu____1584 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1587 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1584 uu____1587 in
                             let uu____1590 =
                               let uu____1591 =
                                 let uu____1594 =
                                   let uu____1600 =
                                     let uu____1601 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1601 in
                                   [uu____1600] in
                                 FStar_Syntax_Util.mk_app x uu____1594 in
                               let uu____1602 =
                                 let uu____1605 =
                                   let uu____1611 =
                                     let uu____1612 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1612 in
                                   [uu____1611] in
                                 FStar_Syntax_Util.mk_app y uu____1605 in
                               mk_rel1 b uu____1591 uu____1602 in
                             FStar_Syntax_Util.mk_imp uu____1583 uu____1590 in
                           let uu____1613 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1613)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___101_1634 = t1 in
                          let uu____1635 =
                            let uu____1636 =
                              let uu____1644 =
                                let uu____1645 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1645 in
                              ([binder], uu____1644) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1636 in
                          {
                            FStar_Syntax_Syntax.n = uu____1635;
                            FStar_Syntax_Syntax.tk =
                              (uu___101_1634.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___101_1634.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___101_1634.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1657 ->
                        failwith "unhandled arrow"
                    | uu____1665 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1680 =
                        let uu____1681 = FStar_Syntax_Subst.compress t1 in
                        uu____1681.FStar_Syntax_Syntax.n in
                      match uu____1680 with
                      | FStar_Syntax_Syntax.Tm_type uu____1684 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1701 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1701
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1716 =
                                let uu____1717 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1717 i in
                              FStar_Syntax_Syntax.fvar uu____1716
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1738 =
                            let uu____1742 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1747  ->
                                     match uu____1747 with
                                     | (t2,q) ->
                                         let uu____1752 = project i x in
                                         let uu____1753 = project i y in
                                         mk_stronger t2 uu____1752 uu____1753)
                                args in
                            match uu____1742 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1738 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1770);
                                      FStar_Syntax_Syntax.tk = uu____1771;
                                      FStar_Syntax_Syntax.pos = uu____1772;
                                      FStar_Syntax_Syntax.vars = uu____1773;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1795  ->
                                   match uu____1795 with
                                   | (bv,q) ->
                                       let uu____1800 =
                                         let uu____1801 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1801 in
                                       FStar_Syntax_Syntax.gen_bv uu____1800
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1805 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1805) bvs in
                          let body =
                            let uu____1807 = FStar_Syntax_Util.mk_app x args in
                            let uu____1808 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1807 uu____1808 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1813);
                                      FStar_Syntax_Syntax.tk = uu____1814;
                                      FStar_Syntax_Syntax.pos = uu____1815;
                                      FStar_Syntax_Syntax.vars = uu____1816;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1838  ->
                                   match uu____1838 with
                                   | (bv,q) ->
                                       let uu____1843 =
                                         let uu____1844 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1844 in
                                       FStar_Syntax_Syntax.gen_bv uu____1843
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1848 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1848) bvs in
                          let body =
                            let uu____1850 = FStar_Syntax_Util.mk_app x args in
                            let uu____1851 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1850 uu____1851 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1854 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1856 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1857 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1858 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1856 uu____1857 uu____1858 in
                    let uu____1859 =
                      let uu____1860 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1860 in
                    FStar_Syntax_Util.abs uu____1859 body ret_tot_type in
                  let stronger1 =
                    let uu____1875 = mk_lid "stronger" in
                    register env1 uu____1875 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1881 = FStar_Util.prefix gamma in
                    match uu____1881 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1907 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1907 in
                          let uu____1910 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1910 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1918 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1918 in
                              let guard_free1 =
                                let uu____1925 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1925 in
                              let pat =
                                let uu____1929 =
                                  let uu____1935 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1935] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1929 in
                              let pattern_guarded_body =
                                let uu____1939 =
                                  let uu____1940 =
                                    let uu____1945 =
                                      let uu____1946 =
                                        let uu____1953 =
                                          let uu____1955 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1955] in
                                        [uu____1953] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1946 in
                                    (body, uu____1945) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1940 in
                                mk1 uu____1939 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1958 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1961 =
                            let uu____1962 =
                              let uu____1963 =
                                let uu____1964 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1967 =
                                  let uu____1973 = args_of_binders1 wp_args in
                                  let uu____1975 =
                                    let uu____1977 =
                                      let uu____1978 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1978 in
                                    [uu____1977] in
                                  FStar_List.append uu____1973 uu____1975 in
                                FStar_Syntax_Util.mk_app uu____1964
                                  uu____1967 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1963 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1962 in
                          FStar_Syntax_Util.abs gamma uu____1961
                            ret_gtot_type in
                        let uu____1979 =
                          let uu____1980 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1980 in
                        FStar_Syntax_Util.abs uu____1979 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1987 = mk_lid "wp_ite" in
                    register env1 uu____1987 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1993 = FStar_Util.prefix gamma in
                    match uu____1993 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2017 =
                            let uu____2018 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2021 =
                              let uu____2027 =
                                let uu____2028 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2028 in
                              [uu____2027] in
                            FStar_Syntax_Util.mk_app uu____2018 uu____2021 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2017 in
                        let uu____2029 =
                          let uu____2030 =
                            let uu____2034 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2034 gamma in
                          FStar_List.append binders uu____2030 in
                        FStar_Syntax_Util.abs uu____2029 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2043 = mk_lid "null_wp" in
                    register env1 uu____2043 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2052 =
                        let uu____2058 =
                          let uu____2060 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2061 =
                            let uu____2063 =
                              let uu____2066 =
                                let uu____2072 =
                                  let uu____2073 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2073 in
                                [uu____2072] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2066 in
                            let uu____2074 =
                              let uu____2078 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2078] in
                            uu____2063 :: uu____2074 in
                          uu____2060 :: uu____2061 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2058 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2052 in
                    let uu____2081 =
                      let uu____2082 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2082 in
                    FStar_Syntax_Util.abs uu____2081 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2089 = mk_lid "wp_trivial" in
                    register env1 uu____2089 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2094 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2094
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2099 =
                      let uu____2101 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2101 in
                    let uu____2106 =
                      let uu___102_2107 = ed in
                      let uu____2108 =
                        let uu____2109 = c wp_if_then_else2 in
                        ([], uu____2109) in
                      let uu____2111 =
                        let uu____2112 = c wp_ite2 in ([], uu____2112) in
                      let uu____2114 =
                        let uu____2115 = c stronger2 in ([], uu____2115) in
                      let uu____2117 =
                        let uu____2118 = c wp_close2 in ([], uu____2118) in
                      let uu____2120 =
                        let uu____2121 = c wp_assert2 in ([], uu____2121) in
                      let uu____2123 =
                        let uu____2124 = c wp_assume2 in ([], uu____2124) in
                      let uu____2126 =
                        let uu____2127 = c null_wp2 in ([], uu____2127) in
                      let uu____2129 =
                        let uu____2130 = c wp_trivial2 in ([], uu____2130) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___102_2107.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___102_2107.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___102_2107.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___102_2107.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___102_2107.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___102_2107.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___102_2107.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2108;
                        FStar_Syntax_Syntax.ite_wp = uu____2111;
                        FStar_Syntax_Syntax.stronger = uu____2114;
                        FStar_Syntax_Syntax.close_wp = uu____2117;
                        FStar_Syntax_Syntax.assert_p = uu____2120;
                        FStar_Syntax_Syntax.assume_p = uu____2123;
                        FStar_Syntax_Syntax.null_wp = uu____2126;
                        FStar_Syntax_Syntax.trivial = uu____2129;
                        FStar_Syntax_Syntax.repr =
                          (uu___102_2107.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___102_2107.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___102_2107.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___102_2107.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2099, uu____2106)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___103_2142 = dmff_env in
      {
        env = env';
        subst = (uu___103_2142.subst);
        tc_const = (uu___103_2142.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2155 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2167 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___89_2177  ->
    match uu___89_2177 with
    | FStar_Syntax_Syntax.Total (t,uu____2179) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___88_2188  ->
                match uu___88_2188 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2189 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2191 =
          let uu____2192 =
            let uu____2193 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2193 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2192 in
        failwith uu____2191
    | FStar_Syntax_Syntax.GTotal uu____2194 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___90_2202  ->
    match uu___90_2202 with
    | N t ->
        let uu____2204 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2204
    | M t ->
        let uu____2206 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2206
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2210,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2212;
                      FStar_Syntax_Syntax.pos = uu____2213;
                      FStar_Syntax_Syntax.vars = uu____2214;_})
        -> nm_of_comp n2
    | uu____2225 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2237 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2237 with | M uu____2238 -> true | N uu____2239 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2243 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2253 =
        let uu____2257 =
          let uu____2258 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2258 in
        [uu____2257] in
      let uu____2259 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2253 uu____2259 in
    let uu____2262 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2262
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
          (let uu____2297 =
             let uu____2305 =
               let uu____2309 =
                 let uu____2312 =
                   let uu____2313 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2313 in
                 let uu____2314 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2312, uu____2314) in
               [uu____2309] in
             let uu____2319 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2305, uu____2319) in
           FStar_Syntax_Syntax.Tm_arrow uu____2297)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2348) ->
          let binders1 =
            FStar_List.map
              (fun uu____2367  ->
                 match uu____2367 with
                 | (bv,aqual) ->
                     let uu____2374 =
                       let uu___104_2375 = bv in
                       let uu____2376 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___104_2375.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___104_2375.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2376
                       } in
                     (uu____2374, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2379,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2381);
                             FStar_Syntax_Syntax.tk = uu____2382;
                             FStar_Syntax_Syntax.pos = uu____2383;
                             FStar_Syntax_Syntax.vars = uu____2384;_})
               ->
               let uu____2401 =
                 let uu____2402 =
                   let uu____2410 =
                     let uu____2411 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2411 in
                   (binders1, uu____2410) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2402 in
               mk1 uu____2401
           | uu____2415 ->
               let uu____2416 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2416 with
                | N hn ->
                    let uu____2418 =
                      let uu____2419 =
                        let uu____2427 =
                          let uu____2428 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2428 in
                        (binders1, uu____2427) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2419 in
                    mk1 uu____2418
                | M a ->
                    let uu____2433 =
                      let uu____2434 =
                        let uu____2442 =
                          let uu____2446 =
                            let uu____2450 =
                              let uu____2453 =
                                let uu____2454 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2454 in
                              let uu____2455 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2453, uu____2455) in
                            [uu____2450] in
                          FStar_List.append binders1 uu____2446 in
                        let uu____2462 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2442, uu____2462) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2434 in
                    mk1 uu____2433))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2513 = f x in
                    FStar_Util.string_builder_append strb uu____2513);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2517 = f x1 in
                         FStar_Util.string_builder_append strb uu____2517))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2519 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2520 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2519 uu____2520 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2528 =
              let uu____2529 = FStar_Syntax_Subst.compress ty in
              uu____2529.FStar_Syntax_Syntax.n in
            match uu____2528 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2544 =
                  let uu____2545 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2545 in
                if uu____2544
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2559 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2559 s in
                       let uu____2561 =
                         let uu____2562 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2562 in
                       if uu____2561
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2565 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2565 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2576  ->
                                  match uu____2576 with
                                  | (bv,uu____2582) ->
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
            | uu____2595 ->
                ((let uu____2597 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2597);
                 false) in
          let rec is_valid_application head2 =
            let uu____2602 =
              let uu____2603 = FStar_Syntax_Subst.compress head2 in
              uu____2603.FStar_Syntax_Syntax.n in
            match uu____2602 with
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
                  (let uu____2607 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2607)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____2609 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____2609 with
                 | ((uu____2614,ty),uu____2616) ->
                     let uu____2619 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____2619
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____2627 -> true
                        | uu____2637 ->
                            ((let uu____2639 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____2639);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____2641 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2642 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2644) ->
                is_valid_application t2
            | uu____2649 -> false in
          let uu____2650 = is_valid_application head1 in
          if uu____2650
          then
            let uu____2651 =
              let uu____2652 =
                let uu____2662 =
                  FStar_List.map
                    (fun uu____2672  ->
                       match uu____2672 with
                       | (t2,qual) ->
                           let uu____2685 = star_type' env t2 in
                           (uu____2685, qual)) args in
                (head1, uu____2662) in
              FStar_Syntax_Syntax.Tm_app uu____2652 in
            mk1 uu____2651
          else
            (let uu____2692 =
               let uu____2693 =
                 let uu____2694 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2694 in
               FStar_Errors.Err uu____2693 in
             raise uu____2692)
      | FStar_Syntax_Syntax.Tm_bvar uu____2695 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2696 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2697 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2698 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2724 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2724 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___107_2730 = env in
                 let uu____2731 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2731;
                   subst = (uu___107_2730.subst);
                   tc_const = (uu___107_2730.tc_const)
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
               ((let uu___108_2748 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___108_2748.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___108_2748.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2755 =
            let uu____2756 =
              let uu____2761 = star_type' env t2 in (uu____2761, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2756 in
          mk1 uu____2755
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2799 =
            let uu____2800 =
              let uu____2818 = star_type' env e in
              let uu____2819 =
                let uu____2829 =
                  let uu____2834 = star_type' env t2 in
                  FStar_Util.Inl uu____2834 in
                (uu____2829, None) in
              (uu____2818, uu____2819, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2800 in
          mk1 uu____2799
      | FStar_Syntax_Syntax.Tm_ascribed uu____2856 ->
          let uu____2874 =
            let uu____2875 =
              let uu____2876 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2876 in
            FStar_Errors.Err uu____2875 in
          raise uu____2874
      | FStar_Syntax_Syntax.Tm_refine uu____2877 ->
          let uu____2882 =
            let uu____2883 =
              let uu____2884 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2884 in
            FStar_Errors.Err uu____2883 in
          raise uu____2882
      | FStar_Syntax_Syntax.Tm_uinst uu____2885 ->
          let uu____2890 =
            let uu____2891 =
              let uu____2892 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2892 in
            FStar_Errors.Err uu____2891 in
          raise uu____2890
      | FStar_Syntax_Syntax.Tm_constant uu____2893 ->
          let uu____2894 =
            let uu____2895 =
              let uu____2896 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2896 in
            FStar_Errors.Err uu____2895 in
          raise uu____2894
      | FStar_Syntax_Syntax.Tm_match uu____2897 ->
          let uu____2912 =
            let uu____2913 =
              let uu____2914 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2914 in
            FStar_Errors.Err uu____2913 in
          raise uu____2912
      | FStar_Syntax_Syntax.Tm_let uu____2915 ->
          let uu____2923 =
            let uu____2924 =
              let uu____2925 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2925 in
            FStar_Errors.Err uu____2924 in
          raise uu____2923
      | FStar_Syntax_Syntax.Tm_uvar uu____2926 ->
          let uu____2937 =
            let uu____2938 =
              let uu____2939 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2939 in
            FStar_Errors.Err uu____2938 in
          raise uu____2937
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2940 =
            let uu____2941 =
              let uu____2942 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2942 in
            FStar_Errors.Err uu____2941 in
          raise uu____2940
      | FStar_Syntax_Syntax.Tm_delayed uu____2943 -> failwith "impossible"
let is_monadic uu___92_2976 =
  match uu___92_2976 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____2988;
        FStar_Syntax_Syntax.res_typ = uu____2989;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____2991;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_3008  ->
              match uu___91_3008 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3009 -> false))
  | Some (FStar_Util.Inr (uu____3010,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_3023  ->
              match uu___91_3023 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3024 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3028 =
      let uu____3029 = FStar_Syntax_Subst.compress t in
      uu____3029.FStar_Syntax_Syntax.n in
    match uu____3028 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3049 =
            let uu____3050 = FStar_List.hd args in fst uu____3050 in
          is_C uu____3049 in
        if r
        then
          ((let uu____3062 =
              let uu____3063 =
                FStar_List.for_all
                  (fun uu____3066  ->
                     match uu____3066 with | (h,uu____3070) -> is_C h) args in
              Prims.op_Negation uu____3063 in
            if uu____3062 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3074 =
              let uu____3075 =
                FStar_List.for_all
                  (fun uu____3078  ->
                     match uu____3078 with
                     | (h,uu____3082) ->
                         let uu____3083 = is_C h in
                         Prims.op_Negation uu____3083) args in
              Prims.op_Negation uu____3075 in
            if uu____3074 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3097 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3097 with
         | M t1 ->
             ((let uu____3100 = is_C t1 in
               if uu____3100 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3104) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3110) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3116,uu____3117) -> is_C t1
    | uu____3146 -> false
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
          let uu____3173 =
            let uu____3174 =
              let uu____3184 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3185 =
                let uu____3189 =
                  let uu____3192 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3192) in
                [uu____3189] in
              (uu____3184, uu____3185) in
            FStar_Syntax_Syntax.Tm_app uu____3174 in
          mk1 uu____3173 in
        let uu____3200 =
          let uu____3201 = FStar_Syntax_Syntax.mk_binder p in [uu____3201] in
        let uu____3202 =
          let uu____3209 =
            let uu____3215 =
              let uu____3216 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3216 in
            FStar_Util.Inl uu____3215 in
          Some uu____3209 in
        FStar_Syntax_Util.abs uu____3200 body uu____3202
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___93_3229  ->
    match uu___93_3229 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3230 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3363 =
          match uu____3363 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3384 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3385 =
                       let uu____3386 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3386 in
                     Prims.op_Negation uu____3385) in
                if uu____3384
                then
                  let uu____3387 =
                    let uu____3388 =
                      let uu____3389 = FStar_Syntax_Print.term_to_string e in
                      let uu____3390 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3391 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3389 uu____3390 uu____3391 in
                    FStar_Errors.Err uu____3388 in
                  raise uu____3387
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3405 = mk_return env t1 s_e in
                     ((M t1), uu____3405, u_e)))
               | (M t1,N t2) ->
                   let uu____3408 =
                     let uu____3409 =
                       let uu____3410 = FStar_Syntax_Print.term_to_string e in
                       let uu____3411 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3412 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3410 uu____3411 uu____3412 in
                     FStar_Errors.Err uu____3409 in
                   raise uu____3408) in
        let ensure_m env1 e2 =
          let strip_m uu___94_3438 =
            match uu___94_3438 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3448 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3459 =
                let uu____3460 =
                  let uu____3463 =
                    let uu____3464 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3464 in
                  (uu____3463, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3460 in
              raise uu____3459
          | M uu____3468 ->
              let uu____3469 = check env1 e2 context_nm in strip_m uu____3469 in
        let uu____3473 =
          let uu____3474 = FStar_Syntax_Subst.compress e in
          uu____3474.FStar_Syntax_Syntax.n in
        match uu____3473 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3480 ->
            let uu____3481 = infer env e in return_if uu____3481
        | FStar_Syntax_Syntax.Tm_name uu____3485 ->
            let uu____3486 = infer env e in return_if uu____3486
        | FStar_Syntax_Syntax.Tm_fvar uu____3490 ->
            let uu____3491 = infer env e in return_if uu____3491
        | FStar_Syntax_Syntax.Tm_abs uu____3495 ->
            let uu____3510 = infer env e in return_if uu____3510
        | FStar_Syntax_Syntax.Tm_constant uu____3514 ->
            let uu____3515 = infer env e in return_if uu____3515
        | FStar_Syntax_Syntax.Tm_app uu____3519 ->
            let uu____3529 = infer env e in return_if uu____3529
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3574) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3580) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3586,uu____3587) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3616 ->
            let uu____3624 =
              let uu____3625 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3625 in
            failwith uu____3624
        | FStar_Syntax_Syntax.Tm_type uu____3629 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3633 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3644 ->
            let uu____3649 =
              let uu____3650 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3650 in
            failwith uu____3649
        | FStar_Syntax_Syntax.Tm_uvar uu____3654 ->
            let uu____3665 =
              let uu____3666 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3666 in
            failwith uu____3665
        | FStar_Syntax_Syntax.Tm_delayed uu____3670 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3694 =
              let uu____3695 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3695 in
            failwith uu____3694
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
      let uu____3717 =
        let uu____3718 = FStar_Syntax_Subst.compress e in
        uu____3718.FStar_Syntax_Syntax.n in
      match uu____3717 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___109_3758 = env in
            let uu____3759 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3759;
              subst = (uu___109_3758.subst);
              tc_const = (uu___109_3758.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3768  ->
                 match uu____3768 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___110_3776 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___110_3776.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___110_3776.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3777 =
            FStar_List.fold_left
              (fun uu____3786  ->
                 fun uu____3787  ->
                   match (uu____3786, uu____3787) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3815 = is_C c in
                       if uu____3815
                       then
                         let xw =
                           let uu____3820 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3820 in
                         let x =
                           let uu___111_3822 = bv in
                           let uu____3823 =
                             let uu____3826 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3826 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___111_3822.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___111_3822.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3823
                           } in
                         let env3 =
                           let uu___112_3828 = env2 in
                           let uu____3829 =
                             let uu____3831 =
                               let uu____3832 =
                                 let uu____3837 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3837) in
                               FStar_Syntax_Syntax.NT uu____3832 in
                             uu____3831 :: (env2.subst) in
                           {
                             env = (uu___112_3828.env);
                             subst = uu____3829;
                             tc_const = (uu___112_3828.tc_const)
                           } in
                         let uu____3838 =
                           let uu____3840 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3841 =
                             let uu____3843 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3843 :: acc in
                           uu____3840 :: uu____3841 in
                         (env3, uu____3838)
                       else
                         (let x =
                            let uu___113_3847 = bv in
                            let uu____3848 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___113_3847.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___113_3847.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3848
                            } in
                          let uu____3851 =
                            let uu____3853 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3853 :: acc in
                          (env2, uu____3851))) (env1, []) binders1 in
          (match uu____3777 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3865 =
                 let check_what =
                   let uu____3877 = is_monadic what in
                   if uu____3877 then check_m else check_n in
                 let uu____3886 = check_what env2 body1 in
                 match uu____3886 with
                 | (t,s_body,u_body) ->
                     let uu____3896 =
                       let uu____3897 =
                         let uu____3898 = is_monadic what in
                         if uu____3898 then M t else N t in
                       comp_of_nm uu____3897 in
                     (uu____3896, s_body, u_body) in
               (match uu____3865 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3941 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___95_3943  ->
                                    match uu___95_3943 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3944 -> false)) in
                          if uu____3941
                          then
                            let double_starred_comp =
                              let uu____3952 =
                                let uu____3953 =
                                  let uu____3954 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____3954 in
                                FStar_All.pipe_left double_star uu____3953 in
                              FStar_Syntax_Syntax.mk_Total uu____3952 in
                            let flags =
                              FStar_List.filter
                                (fun uu___96_3959  ->
                                   match uu___96_3959 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3960 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____3961 =
                              let uu____3967 =
                                let uu____3968 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____3968 in
                              FStar_Util.Inl uu____3967 in
                            Some uu____3961
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___114_3988 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___114_3988.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___114_3988.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___114_3988.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____3989  ->
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
                          let uu____4006 =
                            let uu____4012 =
                              let uu____4016 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___97_4018  ->
                                        match uu___97_4018 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4019 -> false)) in
                              if uu____4016
                              then
                                let uu____4023 =
                                  FStar_List.filter
                                    (fun uu___98_4025  ->
                                       match uu___98_4025 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4026 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4023)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4012 in
                          Some uu____4006 in
                    let uu____4038 =
                      let comp1 =
                        let uu____4050 = is_monadic what in
                        let uu____4051 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4050 uu____4051 in
                      let uu____4052 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4052,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4038 with
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
                FStar_Syntax_Syntax.p = uu____4130;_};
            FStar_Syntax_Syntax.fv_delta = uu____4131;
            FStar_Syntax_Syntax.fv_qual = uu____4132;_}
          ->
          let uu____4134 =
            let uu____4137 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4137 in
          (match uu____4134 with
           | (uu____4153,t) ->
               let uu____4155 = let uu____4156 = normalize1 t in N uu____4156 in
               (uu____4155, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4173 = check_n env head1 in
          (match uu____4173 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4187 =
                   let uu____4188 = FStar_Syntax_Subst.compress t in
                   uu____4188.FStar_Syntax_Syntax.n in
                 match uu____4187 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4191 -> true
                 | uu____4199 -> false in
               let rec flatten1 t =
                 let uu____4211 =
                   let uu____4212 = FStar_Syntax_Subst.compress t in
                   uu____4212.FStar_Syntax_Syntax.n in
                 match uu____4211 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4224);
                                FStar_Syntax_Syntax.tk = uu____4225;
                                FStar_Syntax_Syntax.pos = uu____4226;
                                FStar_Syntax_Syntax.vars = uu____4227;_})
                     when is_arrow t1 ->
                     let uu____4244 = flatten1 t1 in
                     (match uu____4244 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4296,uu____4297)
                     -> flatten1 e1
                 | uu____4326 ->
                     let uu____4327 =
                       let uu____4328 =
                         let uu____4329 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4329 in
                       FStar_Errors.Err uu____4328 in
                     raise uu____4327 in
               let uu____4337 = flatten1 t_head in
               (match uu____4337 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4382 =
                          let uu____4383 =
                            let uu____4384 = FStar_Util.string_of_int n1 in
                            let uu____4388 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4394 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4384 uu____4388 uu____4394 in
                          FStar_Errors.Err uu____4383 in
                        raise uu____4382)
                     else ();
                     (let uu____4399 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4399 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4426 args1 =
                            match uu____4426 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4469 =
                                       let uu____4470 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4470.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4469
                                 | (binders3,[]) ->
                                     let uu____4489 =
                                       let uu____4490 =
                                         let uu____4493 =
                                           let uu____4494 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4494 in
                                         FStar_Syntax_Subst.compress
                                           uu____4493 in
                                       uu____4490.FStar_Syntax_Syntax.n in
                                     (match uu____4489 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4510 =
                                            let uu____4511 =
                                              let uu____4512 =
                                                let uu____4520 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4520) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4512 in
                                            mk1 uu____4511 in
                                          N uu____4510
                                      | uu____4524 -> failwith "wat?")
                                 | ([],uu____4525::uu____4526) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4551)::binders3,(arg,uu____4554)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4588 = FStar_List.splitAt n' binders1 in
                          (match uu____4588 with
                           | (binders2,uu____4605) ->
                               let uu____4618 =
                                 let uu____4628 =
                                   FStar_List.map2
                                     (fun uu____4648  ->
                                        fun uu____4649  ->
                                          match (uu____4648, uu____4649) with
                                          | ((bv,uu____4666),(arg,q)) ->
                                              let uu____4673 =
                                                let uu____4674 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4674.FStar_Syntax_Syntax.n in
                                              (match uu____4673 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4684 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4697 ->
                                                   let uu____4698 =
                                                     check_n env arg in
                                                   (match uu____4698 with
                                                    | (uu____4709,s_arg,u_arg)
                                                        ->
                                                        let uu____4712 =
                                                          let uu____4716 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4716
                                                          then
                                                            let uu____4720 =
                                                              let uu____4723
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4723, q) in
                                                            [uu____4720;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4712))))
                                     binders2 args in
                                 FStar_List.split uu____4628 in
                               (match uu____4618 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4770 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4776 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4770, uu____4776)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4823) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4829) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4835,uu____4836) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4866 = let uu____4867 = env.tc_const c in N uu____4867 in
          (uu____4866, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4868 ->
          let uu____4876 =
            let uu____4877 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4877 in
          failwith uu____4876
      | FStar_Syntax_Syntax.Tm_type uu____4881 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4885 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4896 ->
          let uu____4901 =
            let uu____4902 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4902 in
          failwith uu____4901
      | FStar_Syntax_Syntax.Tm_uvar uu____4906 ->
          let uu____4917 =
            let uu____4918 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4918 in
          failwith uu____4917
      | FStar_Syntax_Syntax.Tm_delayed uu____4922 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4946 =
            let uu____4947 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4947 in
          failwith uu____4946
and mk_match:
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t*
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
          let uu____4984 = check_n env e0 in
          match uu____4984 with
          | (uu____4991,s_e0,u_e0) ->
              let uu____4994 =
                let uu____5011 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5042 = FStar_Syntax_Subst.open_branch b in
                       match uu____5042 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___115_5071 = env in
                             let uu____5072 =
                               let uu____5073 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5073 in
                             {
                               env = uu____5072;
                               subst = (uu___115_5071.subst);
                               tc_const = (uu___115_5071.tc_const)
                             } in
                           let uu____5075 = f env1 body in
                           (match uu____5075 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5121 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5011 in
              (match uu____4994 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5182 = FStar_List.hd nms in
                     match uu____5182 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___99_5186  ->
                          match uu___99_5186 with
                          | M uu____5187 -> true
                          | uu____5188 -> false) nms in
                   let uu____5189 =
                     let uu____5210 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5257  ->
                              match uu____5257 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5365 =
                                         check env original_body (M t2) in
                                       (match uu____5365 with
                                        | (uu____5386,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5411,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5210 in
                   (match uu____5189 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5519  ->
                                 match uu____5519 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5556 =
                                         let uu____5557 =
                                           let uu____5567 =
                                             let uu____5571 =
                                               let uu____5574 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5575 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5574, uu____5575) in
                                             [uu____5571] in
                                           (s_body, uu____5567) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5557 in
                                       mk1 uu____5556 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5596 =
                              let uu____5597 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5597] in
                            let uu____5598 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5600 =
                              let uu____5607 =
                                let uu____5613 =
                                  let uu____5614 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5614 in
                                FStar_Util.Inl uu____5613 in
                              Some uu____5607 in
                            FStar_Syntax_Util.abs uu____5596 uu____5598
                              uu____5600 in
                          let t1_star =
                            let uu____5628 =
                              let uu____5632 =
                                let uu____5633 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5633 in
                              [uu____5632] in
                            let uu____5634 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5628 uu____5634 in
                          let uu____5637 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5667 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5637, uu____5667)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5681 =
                             let uu____5684 =
                               let uu____5685 =
                                 let uu____5703 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5703,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5685 in
                             mk1 uu____5684 in
                           let uu____5730 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5681, uu____5730))))
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
              let uu____5773 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5773] in
            let uu____5774 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5774 with
            | (x_binders1,e21) ->
                let uu____5782 = infer env e1 in
                (match uu____5782 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5793 = is_C t1 in
                       if uu____5793
                       then
                         let uu___116_5794 = binding in
                         let uu____5795 =
                           let uu____5798 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5798 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___116_5794.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___116_5794.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5795;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___116_5794.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___116_5794.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___117_5801 = env in
                       let uu____5802 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___118_5803 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___118_5803.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___118_5803.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5802;
                         subst = (uu___117_5801.subst);
                         tc_const = (uu___117_5801.tc_const)
                       } in
                     let uu____5804 = proceed env1 e21 in
                     (match uu____5804 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___119_5815 = binding in
                            let uu____5816 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___119_5815.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___119_5815.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5816;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___119_5815.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___119_5815.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5819 =
                            let uu____5822 =
                              let uu____5823 =
                                let uu____5831 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___120_5836 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___120_5836.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___120_5836.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___120_5836.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___120_5836.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5831) in
                              FStar_Syntax_Syntax.Tm_let uu____5823 in
                            mk1 uu____5822 in
                          let uu____5837 =
                            let uu____5840 =
                              let uu____5841 =
                                let uu____5849 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___121_5854 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5854.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5854.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5854.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5854.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5849) in
                              FStar_Syntax_Syntax.Tm_let uu____5841 in
                            mk1 uu____5840 in
                          (nm_rec, uu____5819, uu____5837))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___122_5863 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___122_5863.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___122_5863.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___122_5863.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___123_5865 = env in
                       let uu____5866 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___124_5867 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_5867.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_5867.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5866;
                         subst = (uu___123_5865.subst);
                         tc_const = (uu___123_5865.tc_const)
                       } in
                     let uu____5868 = ensure_m env1 e21 in
                     (match uu____5868 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5885 =
                              let uu____5886 =
                                let uu____5896 =
                                  let uu____5900 =
                                    let uu____5903 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5904 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5903, uu____5904) in
                                  [uu____5900] in
                                (s_e2, uu____5896) in
                              FStar_Syntax_Syntax.Tm_app uu____5886 in
                            mk1 uu____5885 in
                          let s_e22 =
                            let uu____5913 =
                              let uu____5920 =
                                let uu____5926 =
                                  let uu____5927 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5927 in
                                FStar_Util.Inl uu____5926 in
                              Some uu____5920 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____5913 in
                          let body =
                            let uu____5941 =
                              let uu____5942 =
                                let uu____5952 =
                                  let uu____5956 =
                                    let uu____5959 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5959) in
                                  [uu____5956] in
                                (s_e1, uu____5952) in
                              FStar_Syntax_Syntax.Tm_app uu____5942 in
                            mk1 uu____5941 in
                          let uu____5967 =
                            let uu____5968 =
                              let uu____5969 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5969] in
                            let uu____5970 =
                              let uu____5977 =
                                let uu____5983 =
                                  let uu____5984 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5984 in
                                FStar_Util.Inl uu____5983 in
                              Some uu____5977 in
                            FStar_Syntax_Util.abs uu____5968 body uu____5970 in
                          let uu____5995 =
                            let uu____5998 =
                              let uu____5999 =
                                let uu____6007 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___125_6012 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_6012.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_6012.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_6012.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_6012.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6007) in
                              FStar_Syntax_Syntax.Tm_let uu____5999 in
                            mk1 uu____5998 in
                          ((M t2), uu____5967, uu____5995)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6021 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6021 in
      let uu____6026 = check env e mn in
      match uu____6026 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6036 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6049 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6049 in
      let uu____6054 = check env e mn in
      match uu____6054 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6064 -> failwith "[check_m]: impossible"
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
        (let uu____6086 =
           let uu____6087 = is_C c in Prims.op_Negation uu____6087 in
         if uu____6086 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6099 =
           let uu____6100 = FStar_Syntax_Subst.compress c in
           uu____6100.FStar_Syntax_Syntax.n in
         match uu____6099 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6119 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6119 with
              | (wp_head,wp_args) ->
                  ((let uu____6146 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6159 =
                           let uu____6160 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6160 in
                         Prims.op_Negation uu____6159) in
                    if uu____6146 then failwith "mismatch" else ());
                   (let uu____6169 =
                      let uu____6170 =
                        let uu____6180 =
                          FStar_List.map2
                            (fun uu____6190  ->
                               fun uu____6191  ->
                                 match (uu____6190, uu____6191) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6214 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6214
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6217 = print_implicit q in
                                         let uu____6218 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6217 uu____6218)
                                      else ();
                                      (let uu____6220 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6220, q)))) args wp_args in
                        (head1, uu____6180) in
                      FStar_Syntax_Syntax.Tm_app uu____6170 in
                    mk1 uu____6169)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6242 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6242 with
              | (binders_orig,comp1) ->
                  let uu____6247 =
                    let uu____6255 =
                      FStar_List.map
                        (fun uu____6269  ->
                           match uu____6269 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6282 = is_C h in
                               if uu____6282
                               then
                                 let w' =
                                   let uu____6289 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6289 in
                                 let uu____6290 =
                                   let uu____6294 =
                                     let uu____6298 =
                                       let uu____6301 =
                                         let uu____6302 =
                                           let uu____6303 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6303 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6302 in
                                       (uu____6301, q) in
                                     [uu____6298] in
                                   (w', q) :: uu____6294 in
                                 (w', uu____6290)
                               else
                                 (let x =
                                    let uu____6315 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6315 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6255 in
                  (match uu____6247 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6345 =
                           let uu____6347 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6347 in
                         FStar_Syntax_Subst.subst_comp uu____6345 comp1 in
                       let app =
                         let uu____6351 =
                           let uu____6352 =
                             let uu____6362 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6369 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6370 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6369, uu____6370)) bvs in
                             (wp, uu____6362) in
                           FStar_Syntax_Syntax.Tm_app uu____6352 in
                         mk1 uu____6351 in
                       let comp3 =
                         let uu____6375 = type_of_comp comp2 in
                         let uu____6376 = is_monadic_comp comp2 in
                         trans_G env uu____6375 uu____6376 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6378,uu____6379) ->
             trans_F_ env e wp
         | uu____6408 -> failwith "impossible trans_F_")
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
            let uu____6413 =
              let uu____6414 = star_type' env h in
              let uu____6417 =
                let uu____6423 =
                  let uu____6426 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6426) in
                [uu____6423] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6414;
                FStar_Syntax_Syntax.effect_args = uu____6417;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6413
          else
            (let uu____6432 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6432)
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
    fun t  -> let uu____6443 = n env.env t in star_type' env uu____6443
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6455 = n env.env t in check_n env uu____6455
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6465 = n env.env c in
        let uu____6466 = n env.env wp in trans_F_ env uu____6465 uu____6466