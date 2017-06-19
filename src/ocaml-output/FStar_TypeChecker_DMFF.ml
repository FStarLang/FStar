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
              let uu___98_68 = a in
              let uu____69 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___98_68.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___98_68.FStar_Syntax_Syntax.index);
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
                  let uu____303 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____304 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____303, uu____304) in
                match uu____269 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____335 =
                        let uu____336 =
                          let uu____346 =
                            let uu____350 =
                              FStar_List.map
                                (fun uu____358  ->
                                   match uu____358 with
                                   | (bv,uu____364) ->
                                       let uu____365 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____366 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____365, uu____366)) binders in
                            let uu____367 =
                              let uu____371 =
                                let uu____374 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____375 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____374, uu____375) in
                              let uu____376 =
                                let uu____380 =
                                  let uu____383 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____383) in
                                [uu____380] in
                              uu____371 :: uu____376 in
                            FStar_List.append uu____350 uu____367 in
                          (fv, uu____346) in
                        FStar_Syntax_Syntax.Tm_app uu____336 in
                      mk1 uu____335 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____257 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____429 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____429 in
                    let ret1 =
                      let uu____432 =
                        let uu____433 =
                          let uu____436 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____436 in
                        FStar_Syntax_Util.residual_tot uu____433 in
                      Some uu____432 in
                    let body =
                      let uu____438 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____438 ret1 in
                    let uu____439 =
                      let uu____440 = mk_all_implicit binders in
                      let uu____444 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____440 uu____444 in
                    FStar_Syntax_Util.abs uu____439 body ret1 in
                  let c_pure1 =
                    let uu____459 = mk_lid "pure" in
                    register env1 uu____459 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____464 =
                        let uu____465 =
                          let uu____466 =
                            let uu____470 =
                              let uu____471 =
                                let uu____472 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____472 in
                              FStar_Syntax_Syntax.mk_binder uu____471 in
                            [uu____470] in
                          let uu____473 =
                            let uu____476 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____476 in
                          FStar_Syntax_Util.arrow uu____466 uu____473 in
                        mk_gctx uu____465 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____464 in
                    let r =
                      let uu____478 =
                        let uu____479 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____479 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____478 in
                    let ret1 =
                      let uu____482 =
                        let uu____483 =
                          let uu____486 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____486 in
                        FStar_Syntax_Util.residual_tot uu____483 in
                      Some uu____482 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____493 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____496 =
                          let uu____502 =
                            let uu____504 =
                              let uu____505 =
                                let uu____506 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____506
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____505 in
                            [uu____504] in
                          FStar_List.append gamma_as_args uu____502 in
                        FStar_Syntax_Util.mk_app uu____493 uu____496 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____509 =
                      let uu____510 = mk_all_implicit binders in
                      let uu____514 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____510 uu____514 in
                    FStar_Syntax_Util.abs uu____509 outer_body ret1 in
                  let c_app1 =
                    let uu____533 = mk_lid "app" in
                    register env1 uu____533 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____540 =
                        let uu____544 =
                          let uu____545 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____545 in
                        [uu____544] in
                      let uu____546 =
                        let uu____549 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____549 in
                      FStar_Syntax_Util.arrow uu____540 uu____546 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____552 =
                        let uu____553 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____553 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____552 in
                    let ret1 =
                      let uu____556 =
                        let uu____557 =
                          let uu____560 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____560 in
                        FStar_Syntax_Util.residual_tot uu____557 in
                      Some uu____556 in
                    let uu____561 =
                      let uu____562 = mk_all_implicit binders in
                      let uu____566 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____562 uu____566 in
                    let uu____584 =
                      let uu____585 =
                        let uu____591 =
                          let uu____593 =
                            let uu____596 =
                              let uu____602 =
                                let uu____604 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____604] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____602 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____596 in
                          let uu____605 =
                            let uu____609 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____609] in
                          uu____593 :: uu____605 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____591 in
                      FStar_Syntax_Util.mk_app c_app1 uu____585 in
                    FStar_Syntax_Util.abs uu____561 uu____584 ret1 in
                  let c_lift11 =
                    let uu____613 = mk_lid "lift1" in
                    register env1 uu____613 c_lift1 in
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
                      let uu____621 =
                        let uu____625 =
                          let uu____626 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____626 in
                        let uu____627 =
                          let uu____629 =
                            let uu____630 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____630 in
                          [uu____629] in
                        uu____625 :: uu____627 in
                      let uu____631 =
                        let uu____634 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____634 in
                      FStar_Syntax_Util.arrow uu____621 uu____631 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____637 =
                        let uu____638 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____638 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____637 in
                    let a2 =
                      let uu____640 =
                        let uu____641 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____641 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____640 in
                    let ret1 =
                      let uu____644 =
                        let uu____645 =
                          let uu____648 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____648 in
                        FStar_Syntax_Util.residual_tot uu____645 in
                      Some uu____644 in
                    let uu____649 =
                      let uu____650 = mk_all_implicit binders in
                      let uu____654 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____650 uu____654 in
                    let uu____676 =
                      let uu____677 =
                        let uu____683 =
                          let uu____685 =
                            let uu____688 =
                              let uu____694 =
                                let uu____696 =
                                  let uu____699 =
                                    let uu____705 =
                                      let uu____707 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____707] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____705 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____699 in
                                let uu____708 =
                                  let uu____712 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____712] in
                                uu____696 :: uu____708 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____694 in
                            FStar_Syntax_Util.mk_app c_app1 uu____688 in
                          let uu____715 =
                            let uu____719 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____719] in
                          uu____685 :: uu____715 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____683 in
                      FStar_Syntax_Util.mk_app c_app1 uu____677 in
                    FStar_Syntax_Util.abs uu____649 uu____676 ret1 in
                  let c_lift21 =
                    let uu____723 = mk_lid "lift2" in
                    register env1 uu____723 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____730 =
                        let uu____734 =
                          let uu____735 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____735 in
                        [uu____734] in
                      let uu____736 =
                        let uu____739 =
                          let uu____740 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____740 in
                        FStar_Syntax_Syntax.mk_Total uu____739 in
                      FStar_Syntax_Util.arrow uu____730 uu____736 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____744 =
                        let uu____745 =
                          let uu____748 =
                            let uu____749 =
                              let uu____753 =
                                let uu____754 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____754 in
                              [uu____753] in
                            let uu____755 =
                              let uu____758 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____758 in
                            FStar_Syntax_Util.arrow uu____749 uu____755 in
                          mk_ctx uu____748 in
                        FStar_Syntax_Util.residual_tot uu____745 in
                      Some uu____744 in
                    let e1 =
                      let uu____760 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____760 in
                    let body =
                      let uu____762 =
                        let uu____763 =
                          let uu____767 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____767] in
                        FStar_List.append gamma uu____763 in
                      let uu____770 =
                        let uu____771 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____774 =
                          let uu____780 =
                            let uu____781 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____781 in
                          let uu____782 = args_of_binders1 gamma in uu____780
                            :: uu____782 in
                        FStar_Syntax_Util.mk_app uu____771 uu____774 in
                      FStar_Syntax_Util.abs uu____762 uu____770 ret1 in
                    let uu____784 =
                      let uu____785 = mk_all_implicit binders in
                      let uu____789 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____785 uu____789 in
                    FStar_Syntax_Util.abs uu____784 body ret1 in
                  let c_push1 =
                    let uu____806 = mk_lid "push" in
                    register env1 uu____806 c_push in
                  let ret_tot_wp_a =
                    Some (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____826 =
                        let uu____827 =
                          let uu____837 = args_of_binders1 binders in
                          (c, uu____837) in
                        FStar_Syntax_Syntax.Tm_app uu____827 in
                      mk1 uu____826
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____845 =
                        let uu____846 =
                          let uu____850 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____851 =
                            let uu____853 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____853] in
                          uu____850 :: uu____851 in
                        let uu____854 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____846 uu____854 in
                      FStar_Syntax_Syntax.mk_Total uu____845 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____858 =
                      let uu____859 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____859 in
                    let uu____865 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____867 =
                        let uu____870 =
                          let uu____876 =
                            let uu____878 =
                              let uu____881 =
                                let uu____887 =
                                  let uu____888 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____888 in
                                [uu____887] in
                              FStar_Syntax_Util.mk_app l_ite uu____881 in
                            [uu____878] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg uu____876 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____870 in
                      FStar_Syntax_Util.ascribe uu____867
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____858 uu____865
                      (Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____905 = mk_lid "wp_if_then_else" in
                    register env1 uu____905 wp_if_then_else in
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
                      let uu____916 =
                        let uu____922 =
                          let uu____924 =
                            let uu____927 =
                              let uu____933 =
                                let uu____935 =
                                  let uu____938 =
                                    let uu____944 =
                                      let uu____945 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____945 in
                                    [uu____944] in
                                  FStar_Syntax_Util.mk_app l_and uu____938 in
                                [uu____935] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____933 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____927 in
                          let uu____950 =
                            let uu____954 = FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____954] in
                          uu____924 :: uu____950 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____922 in
                      FStar_Syntax_Util.mk_app c_app1 uu____916 in
                    let uu____957 =
                      let uu____958 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____958 in
                    FStar_Syntax_Util.abs uu____957 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____965 = mk_lid "wp_assert" in
                    register env1 uu____965 wp_assert in
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
                      let uu____976 =
                        let uu____982 =
                          let uu____984 =
                            let uu____987 =
                              let uu____993 =
                                let uu____995 =
                                  let uu____998 =
                                    let uu____1004 =
                                      let uu____1005 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1005 in
                                    [uu____1004] in
                                  FStar_Syntax_Util.mk_app l_imp uu____998 in
                                [uu____995] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____993 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____987 in
                          let uu____1010 =
                            let uu____1014 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1014] in
                          uu____984 :: uu____1010 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____982 in
                      FStar_Syntax_Util.mk_app c_app1 uu____976 in
                    let uu____1017 =
                      let uu____1018 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1018 in
                    FStar_Syntax_Util.abs uu____1017 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1025 = mk_lid "wp_assume" in
                    register env1 uu____1025 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1034 =
                        let uu____1038 =
                          let uu____1039 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1039 in
                        [uu____1038] in
                      let uu____1040 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1034 uu____1040 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1047 =
                        let uu____1053 =
                          let uu____1055 =
                            let uu____1058 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1058 in
                          let uu____1064 =
                            let uu____1068 =
                              let uu____1071 =
                                let uu____1077 =
                                  let uu____1079 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1079] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1077 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1071 in
                            [uu____1068] in
                          uu____1055 :: uu____1064 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1053 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1047 in
                    let uu____1086 =
                      let uu____1087 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1087 in
                    FStar_Syntax_Util.abs uu____1086 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1094 = mk_lid "wp_close" in
                    register env1 uu____1094 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1102 =
                      let uu____1103 =
                        let uu____1104 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1104 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1103 in
                    Some uu____1102 in
                  let mk_forall1 x body =
                    let uu____1116 =
                      let uu____1119 =
                        let uu____1120 =
                          let uu____1130 =
                            let uu____1132 =
                              let uu____1133 =
                                let uu____1134 =
                                  let uu____1135 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1135] in
                                FStar_Syntax_Util.abs uu____1134 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1133 in
                            [uu____1132] in
                          (FStar_Syntax_Util.tforall, uu____1130) in
                        FStar_Syntax_Syntax.Tm_app uu____1120 in
                      FStar_Syntax_Syntax.mk uu____1119 in
                    uu____1116 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1149 =
                      let uu____1150 = FStar_Syntax_Subst.compress t in
                      uu____1150.FStar_Syntax_Syntax.n in
                    match uu____1149 with
                    | FStar_Syntax_Syntax.Tm_type uu____1153 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1168  ->
                              match uu____1168 with
                              | (b,uu____1172) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1173 -> true in
                  let rec is_monotonic t =
                    let uu____1178 =
                      let uu____1179 = FStar_Syntax_Subst.compress t in
                      uu____1179.FStar_Syntax_Syntax.n in
                    match uu____1178 with
                    | FStar_Syntax_Syntax.Tm_type uu____1182 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1197  ->
                              match uu____1197 with
                              | (b,uu____1201) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1202 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1254 =
                      let uu____1255 = FStar_Syntax_Subst.compress t1 in
                      uu____1255.FStar_Syntax_Syntax.n in
                    match uu____1254 with
                    | FStar_Syntax_Syntax.Tm_type uu____1258 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1261);
                                      FStar_Syntax_Syntax.tk = uu____1262;
                                      FStar_Syntax_Syntax.pos = uu____1263;
                                      FStar_Syntax_Syntax.vars = uu____1264;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1287 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1287
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1290 =
                              let uu____1293 =
                                let uu____1299 =
                                  let uu____1300 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1300 in
                                [uu____1299] in
                              FStar_Syntax_Util.mk_app x uu____1293 in
                            let uu____1301 =
                              let uu____1304 =
                                let uu____1310 =
                                  let uu____1311 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1311 in
                                [uu____1310] in
                              FStar_Syntax_Util.mk_app y uu____1304 in
                            mk_rel1 b uu____1290 uu____1301 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1316 =
                               let uu____1317 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1320 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1317 uu____1320 in
                             let uu____1323 =
                               let uu____1324 =
                                 let uu____1327 =
                                   let uu____1333 =
                                     let uu____1334 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1334 in
                                   [uu____1333] in
                                 FStar_Syntax_Util.mk_app x uu____1327 in
                               let uu____1335 =
                                 let uu____1338 =
                                   let uu____1344 =
                                     let uu____1345 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1345 in
                                   [uu____1344] in
                                 FStar_Syntax_Util.mk_app y uu____1338 in
                               mk_rel1 b uu____1324 uu____1335 in
                             FStar_Syntax_Util.mk_imp uu____1316 uu____1323 in
                           let uu____1346 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1346)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1349);
                                      FStar_Syntax_Syntax.tk = uu____1350;
                                      FStar_Syntax_Syntax.pos = uu____1351;
                                      FStar_Syntax_Syntax.vars = uu____1352;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1375 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1375
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1378 =
                              let uu____1381 =
                                let uu____1387 =
                                  let uu____1388 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1388 in
                                [uu____1387] in
                              FStar_Syntax_Util.mk_app x uu____1381 in
                            let uu____1389 =
                              let uu____1392 =
                                let uu____1398 =
                                  let uu____1399 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1399 in
                                [uu____1398] in
                              FStar_Syntax_Util.mk_app y uu____1392 in
                            mk_rel1 b uu____1378 uu____1389 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1404 =
                               let uu____1405 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1408 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1405 uu____1408 in
                             let uu____1411 =
                               let uu____1412 =
                                 let uu____1415 =
                                   let uu____1421 =
                                     let uu____1422 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1422 in
                                   [uu____1421] in
                                 FStar_Syntax_Util.mk_app x uu____1415 in
                               let uu____1423 =
                                 let uu____1426 =
                                   let uu____1432 =
                                     let uu____1433 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1433 in
                                   [uu____1432] in
                                 FStar_Syntax_Util.mk_app y uu____1426 in
                               mk_rel1 b uu____1412 uu____1423 in
                             FStar_Syntax_Util.mk_imp uu____1404 uu____1411 in
                           let uu____1434 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1434)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___99_1455 = t1 in
                          let uu____1456 =
                            let uu____1457 =
                              let uu____1465 =
                                let uu____1466 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1466 in
                              ([binder], uu____1465) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1457 in
                          {
                            FStar_Syntax_Syntax.n = uu____1456;
                            FStar_Syntax_Syntax.tk =
                              (uu___99_1455.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___99_1455.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___99_1455.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1478 ->
                        failwith "unhandled arrow"
                    | uu____1486 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1501 =
                        let uu____1502 = FStar_Syntax_Subst.compress t1 in
                        uu____1502.FStar_Syntax_Syntax.n in
                      match uu____1501 with
                      | FStar_Syntax_Syntax.Tm_type uu____1505 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1522 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1522
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1537 =
                                let uu____1538 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1538 i in
                              FStar_Syntax_Syntax.fvar uu____1537
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1559 =
                            let uu____1563 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1568  ->
                                     match uu____1568 with
                                     | (t2,q) ->
                                         let uu____1573 = project i x in
                                         let uu____1574 = project i y in
                                         mk_stronger t2 uu____1573 uu____1574)
                                args in
                            match uu____1563 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1559 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1591);
                                      FStar_Syntax_Syntax.tk = uu____1592;
                                      FStar_Syntax_Syntax.pos = uu____1593;
                                      FStar_Syntax_Syntax.vars = uu____1594;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1616  ->
                                   match uu____1616 with
                                   | (bv,q) ->
                                       let uu____1621 =
                                         let uu____1622 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1622 in
                                       FStar_Syntax_Syntax.gen_bv uu____1621
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1626 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1626) bvs in
                          let body =
                            let uu____1628 = FStar_Syntax_Util.mk_app x args in
                            let uu____1629 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1628 uu____1629 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1634);
                                      FStar_Syntax_Syntax.tk = uu____1635;
                                      FStar_Syntax_Syntax.pos = uu____1636;
                                      FStar_Syntax_Syntax.vars = uu____1637;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1659  ->
                                   match uu____1659 with
                                   | (bv,q) ->
                                       let uu____1664 =
                                         let uu____1665 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1665 in
                                       FStar_Syntax_Syntax.gen_bv uu____1664
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1669 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1669) bvs in
                          let body =
                            let uu____1671 = FStar_Syntax_Util.mk_app x args in
                            let uu____1672 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1671 uu____1672 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1675 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1677 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1678 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1679 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1677 uu____1678 uu____1679 in
                    let uu____1680 =
                      let uu____1681 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1681 in
                    FStar_Syntax_Util.abs uu____1680 body ret_tot_type in
                  let stronger1 =
                    let uu____1696 = mk_lid "stronger" in
                    register env1 uu____1696 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1702 = FStar_Util.prefix gamma in
                    match uu____1702 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1728 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1728 in
                          let uu____1731 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1731 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1739 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1739 in
                              let guard_free1 =
                                let uu____1746 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1746 in
                              let pat =
                                let uu____1750 =
                                  let uu____1756 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1756] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1750 in
                              let pattern_guarded_body =
                                let uu____1760 =
                                  let uu____1761 =
                                    let uu____1766 =
                                      let uu____1767 =
                                        let uu____1774 =
                                          let uu____1776 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1776] in
                                        [uu____1774] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1767 in
                                    (body, uu____1766) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1761 in
                                mk1 uu____1760 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1779 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1782 =
                            let uu____1783 =
                              let uu____1784 =
                                let uu____1785 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1788 =
                                  let uu____1794 = args_of_binders1 wp_args in
                                  let uu____1796 =
                                    let uu____1798 =
                                      let uu____1799 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1799 in
                                    [uu____1798] in
                                  FStar_List.append uu____1794 uu____1796 in
                                FStar_Syntax_Util.mk_app uu____1785
                                  uu____1788 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1784 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1783 in
                          FStar_Syntax_Util.abs gamma uu____1782
                            ret_gtot_type in
                        let uu____1800 =
                          let uu____1801 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1801 in
                        FStar_Syntax_Util.abs uu____1800 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1808 = mk_lid "wp_ite" in
                    register env1 uu____1808 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1814 = FStar_Util.prefix gamma in
                    match uu____1814 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1838 =
                            let uu____1839 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____1842 =
                              let uu____1848 =
                                let uu____1849 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1849 in
                              [uu____1848] in
                            FStar_Syntax_Util.mk_app uu____1839 uu____1842 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1838 in
                        let uu____1850 =
                          let uu____1851 =
                            let uu____1855 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1855 gamma in
                          FStar_List.append binders uu____1851 in
                        FStar_Syntax_Util.abs uu____1850 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1864 = mk_lid "null_wp" in
                    register env1 uu____1864 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____1873 =
                        let uu____1879 =
                          let uu____1881 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____1882 =
                            let uu____1884 =
                              let uu____1887 =
                                let uu____1893 =
                                  let uu____1894 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____1894 in
                                [uu____1893] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1887 in
                            let uu____1895 =
                              let uu____1899 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____1899] in
                            uu____1884 :: uu____1895 in
                          uu____1881 :: uu____1882 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1879 in
                      FStar_Syntax_Util.mk_app stronger2 uu____1873 in
                    let uu____1902 =
                      let uu____1903 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____1903 in
                    FStar_Syntax_Util.abs uu____1902 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____1910 = mk_lid "wp_trivial" in
                    register env1 uu____1910 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____1915 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____1915
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____1920 =
                      let uu____1922 = FStar_ST.read sigelts in
                      FStar_List.rev uu____1922 in
                    let uu____1927 =
                      let uu___100_1928 = ed in
                      let uu____1929 =
                        let uu____1930 = c wp_if_then_else2 in
                        ([], uu____1930) in
                      let uu____1932 =
                        let uu____1933 = c wp_ite2 in ([], uu____1933) in
                      let uu____1935 =
                        let uu____1936 = c stronger2 in ([], uu____1936) in
                      let uu____1938 =
                        let uu____1939 = c wp_close2 in ([], uu____1939) in
                      let uu____1941 =
                        let uu____1942 = c wp_assert2 in ([], uu____1942) in
                      let uu____1944 =
                        let uu____1945 = c wp_assume2 in ([], uu____1945) in
                      let uu____1947 =
                        let uu____1948 = c null_wp2 in ([], uu____1948) in
                      let uu____1950 =
                        let uu____1951 = c wp_trivial2 in ([], uu____1951) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___100_1928.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___100_1928.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___100_1928.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___100_1928.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___100_1928.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___100_1928.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___100_1928.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____1929;
                        FStar_Syntax_Syntax.ite_wp = uu____1932;
                        FStar_Syntax_Syntax.stronger = uu____1935;
                        FStar_Syntax_Syntax.close_wp = uu____1938;
                        FStar_Syntax_Syntax.assert_p = uu____1941;
                        FStar_Syntax_Syntax.assume_p = uu____1944;
                        FStar_Syntax_Syntax.null_wp = uu____1947;
                        FStar_Syntax_Syntax.trivial = uu____1950;
                        FStar_Syntax_Syntax.repr =
                          (uu___100_1928.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___100_1928.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___100_1928.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___100_1928.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____1920, uu____1927)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___101_1963 = dmff_env in
      {
        env = env';
        subst = (uu___101_1963.subst);
        tc_const = (uu___101_1963.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____1976 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____1988 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___89_1998  ->
    match uu___89_1998 with
    | FStar_Syntax_Syntax.Total (t,uu____2000) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___88_2009  ->
                match uu___88_2009 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2010 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2012 =
          let uu____2013 =
            let uu____2014 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2014 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2013 in
        failwith uu____2012
    | FStar_Syntax_Syntax.GTotal uu____2015 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___90_2023  ->
    match uu___90_2023 with
    | N t ->
        let uu____2025 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2025
    | M t ->
        let uu____2027 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2027
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2031,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2033;
                      FStar_Syntax_Syntax.pos = uu____2034;
                      FStar_Syntax_Syntax.vars = uu____2035;_})
        -> nm_of_comp n2
    | uu____2046 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2058 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2058 with | M uu____2059 -> true | N uu____2060 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2064 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2074 =
        let uu____2078 =
          let uu____2079 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2079 in
        [uu____2078] in
      let uu____2080 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2074 uu____2080 in
    let uu____2083 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2083
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
          (let uu____2118 =
             let uu____2126 =
               let uu____2130 =
                 let uu____2133 =
                   let uu____2134 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2134 in
                 let uu____2135 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2133, uu____2135) in
               [uu____2130] in
             let uu____2140 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2126, uu____2140) in
           FStar_Syntax_Syntax.Tm_arrow uu____2118)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2169) ->
          let binders1 =
            FStar_List.map
              (fun uu____2188  ->
                 match uu____2188 with
                 | (bv,aqual) ->
                     let uu____2195 =
                       let uu___102_2196 = bv in
                       let uu____2197 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___102_2196.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___102_2196.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2197
                       } in
                     (uu____2195, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2200,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2202);
                             FStar_Syntax_Syntax.tk = uu____2203;
                             FStar_Syntax_Syntax.pos = uu____2204;
                             FStar_Syntax_Syntax.vars = uu____2205;_})
               ->
               let uu____2222 =
                 let uu____2223 =
                   let uu____2231 =
                     let uu____2232 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2232 in
                   (binders1, uu____2231) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2223 in
               mk1 uu____2222
           | uu____2236 ->
               let uu____2237 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2237 with
                | N hn ->
                    let uu____2239 =
                      let uu____2240 =
                        let uu____2248 =
                          let uu____2249 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2249 in
                        (binders1, uu____2248) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2240 in
                    mk1 uu____2239
                | M a ->
                    let uu____2254 =
                      let uu____2255 =
                        let uu____2263 =
                          let uu____2267 =
                            let uu____2271 =
                              let uu____2274 =
                                let uu____2275 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2275 in
                              let uu____2276 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2274, uu____2276) in
                            [uu____2271] in
                          FStar_List.append binders1 uu____2267 in
                        let uu____2283 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2263, uu____2283) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2255 in
                    mk1 uu____2254))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2334 = f x in
                    FStar_Util.string_builder_append strb uu____2334);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2338 = f x1 in
                         FStar_Util.string_builder_append strb uu____2338))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2340 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2341 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2340 uu____2341 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2349 =
              let uu____2350 = FStar_Syntax_Subst.compress ty in
              uu____2350.FStar_Syntax_Syntax.n in
            match uu____2349 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2365 =
                  let uu____2366 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2366 in
                if uu____2365
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2380 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2380 s in
                       let uu____2382 =
                         let uu____2383 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2383 in
                       if uu____2382
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2386 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2386 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2397  ->
                                  match uu____2397 with
                                  | (bv,uu____2403) ->
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
            | uu____2416 ->
                ((let uu____2418 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2418);
                 false) in
          let rec is_valid_application head2 =
            let uu____2423 =
              let uu____2424 = FStar_Syntax_Subst.compress head2 in
              uu____2424.FStar_Syntax_Syntax.n in
            match uu____2423 with
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
                  (let uu____2428 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2428)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2441 -> true
                 | uu____2451 ->
                     ((let uu____2453 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2453);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2454 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2455 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2457) ->
                is_valid_application t2
            | uu____2462 -> false in
          let uu____2463 = is_valid_application head1 in
          if uu____2463
          then
            let uu____2464 =
              let uu____2465 =
                let uu____2475 =
                  FStar_List.map
                    (fun uu____2485  ->
                       match uu____2485 with
                       | (t2,qual) ->
                           let uu____2498 = star_type' env t2 in
                           (uu____2498, qual)) args in
                (head1, uu____2475) in
              FStar_Syntax_Syntax.Tm_app uu____2465 in
            mk1 uu____2464
          else
            (let uu____2505 =
               let uu____2506 =
                 let uu____2507 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2507 in
               FStar_Errors.Err uu____2506 in
             raise uu____2505)
      | FStar_Syntax_Syntax.Tm_bvar uu____2508 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2509 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2510 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2511 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2527 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2527 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___105_2533 = env in
                 let uu____2534 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2534;
                   subst = (uu___105_2533.subst);
                   tc_const = (uu___105_2533.tc_const)
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
               ((let uu___106_2551 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___106_2551.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___106_2551.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2558 =
            let uu____2559 =
              let uu____2564 = star_type' env t2 in (uu____2564, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2559 in
          mk1 uu____2558
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2602 =
            let uu____2603 =
              let uu____2621 = star_type' env e in
              let uu____2622 =
                let uu____2632 =
                  let uu____2637 = star_type' env t2 in
                  FStar_Util.Inl uu____2637 in
                (uu____2632, None) in
              (uu____2621, uu____2622, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2603 in
          mk1 uu____2602
      | FStar_Syntax_Syntax.Tm_ascribed uu____2659 ->
          let uu____2677 =
            let uu____2678 =
              let uu____2679 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2679 in
            FStar_Errors.Err uu____2678 in
          raise uu____2677
      | FStar_Syntax_Syntax.Tm_refine uu____2680 ->
          let uu____2685 =
            let uu____2686 =
              let uu____2687 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2687 in
            FStar_Errors.Err uu____2686 in
          raise uu____2685
      | FStar_Syntax_Syntax.Tm_uinst uu____2688 ->
          let uu____2693 =
            let uu____2694 =
              let uu____2695 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2695 in
            FStar_Errors.Err uu____2694 in
          raise uu____2693
      | FStar_Syntax_Syntax.Tm_constant uu____2696 ->
          let uu____2697 =
            let uu____2698 =
              let uu____2699 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2699 in
            FStar_Errors.Err uu____2698 in
          raise uu____2697
      | FStar_Syntax_Syntax.Tm_match uu____2700 ->
          let uu____2716 =
            let uu____2717 =
              let uu____2718 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2718 in
            FStar_Errors.Err uu____2717 in
          raise uu____2716
      | FStar_Syntax_Syntax.Tm_let uu____2719 ->
          let uu____2727 =
            let uu____2728 =
              let uu____2729 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2729 in
            FStar_Errors.Err uu____2728 in
          raise uu____2727
      | FStar_Syntax_Syntax.Tm_uvar uu____2730 ->
          let uu____2739 =
            let uu____2740 =
              let uu____2741 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2741 in
            FStar_Errors.Err uu____2740 in
          raise uu____2739
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2742 =
            let uu____2743 =
              let uu____2744 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2744 in
            FStar_Errors.Err uu____2743 in
          raise uu____2742
      | FStar_Syntax_Syntax.Tm_delayed uu____2745 -> failwith "impossible"
let is_monadic: FStar_Syntax_Syntax.residual_comp option -> Prims.bool =
  fun uu___92_2763  ->
    match uu___92_2763 with
    | None  -> failwith "un-annotated lambda?!"
    | Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___91_2767  ->
                match uu___91_2767 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2768 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2772 =
      let uu____2773 = FStar_Syntax_Subst.compress t in
      uu____2773.FStar_Syntax_Syntax.n in
    match uu____2772 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2793 =
            let uu____2794 = FStar_List.hd args in fst uu____2794 in
          is_C uu____2793 in
        if r
        then
          ((let uu____2806 =
              let uu____2807 =
                FStar_List.for_all
                  (fun uu____2810  ->
                     match uu____2810 with | (h,uu____2814) -> is_C h) args in
              Prims.op_Negation uu____2807 in
            if uu____2806 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2818 =
              let uu____2819 =
                FStar_List.for_all
                  (fun uu____2822  ->
                     match uu____2822 with
                     | (h,uu____2826) ->
                         let uu____2827 = is_C h in
                         Prims.op_Negation uu____2827) args in
              Prims.op_Negation uu____2819 in
            if uu____2818 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2841 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____2841 with
         | M t1 ->
             ((let uu____2844 = is_C t1 in
               if uu____2844 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2848) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2854) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2860,uu____2861) -> is_C t1
    | uu____2890 -> false
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
          let uu____2917 =
            let uu____2918 =
              let uu____2928 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____2929 =
                let uu____2933 =
                  let uu____2936 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____2936) in
                [uu____2933] in
              (uu____2928, uu____2929) in
            FStar_Syntax_Syntax.Tm_app uu____2918 in
          mk1 uu____2917 in
        let uu____2944 =
          let uu____2945 = FStar_Syntax_Syntax.mk_binder p in [uu____2945] in
        FStar_Syntax_Util.abs uu____2944 body
          (Some (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___93_2948  ->
    match uu___93_2948 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____2949 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3083 =
          match uu____3083 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3104 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3105 =
                       let uu____3106 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3106 in
                     Prims.op_Negation uu____3105) in
                if uu____3104
                then
                  let uu____3107 =
                    let uu____3108 =
                      let uu____3109 = FStar_Syntax_Print.term_to_string e in
                      let uu____3110 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3111 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3109 uu____3110 uu____3111 in
                    FStar_Errors.Err uu____3108 in
                  raise uu____3107
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3125 = mk_return env t1 s_e in
                     ((M t1), uu____3125, u_e)))
               | (M t1,N t2) ->
                   let uu____3128 =
                     let uu____3129 =
                       let uu____3130 = FStar_Syntax_Print.term_to_string e in
                       let uu____3131 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3132 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3130 uu____3131 uu____3132 in
                     FStar_Errors.Err uu____3129 in
                   raise uu____3128) in
        let ensure_m env1 e2 =
          let strip_m uu___94_3158 =
            match uu___94_3158 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3168 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3179 =
                let uu____3180 =
                  let uu____3183 =
                    let uu____3184 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3184 in
                  (uu____3183, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3180 in
              raise uu____3179
          | M uu____3188 ->
              let uu____3189 = check env1 e2 context_nm in strip_m uu____3189 in
        let uu____3193 =
          let uu____3194 = FStar_Syntax_Subst.compress e in
          uu____3194.FStar_Syntax_Syntax.n in
        match uu____3193 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3200 ->
            let uu____3201 = infer env e in return_if uu____3201
        | FStar_Syntax_Syntax.Tm_name uu____3205 ->
            let uu____3206 = infer env e in return_if uu____3206
        | FStar_Syntax_Syntax.Tm_fvar uu____3210 ->
            let uu____3211 = infer env e in return_if uu____3211
        | FStar_Syntax_Syntax.Tm_abs uu____3215 ->
            let uu____3225 = infer env e in return_if uu____3225
        | FStar_Syntax_Syntax.Tm_constant uu____3229 ->
            let uu____3230 = infer env e in return_if uu____3230
        | FStar_Syntax_Syntax.Tm_app uu____3234 ->
            let uu____3244 = infer env e in return_if uu____3244
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3291) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3297) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3303,uu____3304) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3333 ->
            let uu____3341 =
              let uu____3342 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3342 in
            failwith uu____3341
        | FStar_Syntax_Syntax.Tm_type uu____3346 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3350 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3361 ->
            let uu____3366 =
              let uu____3367 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3367 in
            failwith uu____3366
        | FStar_Syntax_Syntax.Tm_uvar uu____3371 ->
            let uu____3380 =
              let uu____3381 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3381 in
            failwith uu____3380
        | FStar_Syntax_Syntax.Tm_delayed uu____3385 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3403 =
              let uu____3404 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3404 in
            failwith uu____3403
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
      let uu____3426 =
        let uu____3427 = FStar_Syntax_Subst.compress e in
        uu____3427.FStar_Syntax_Syntax.n in
      match uu____3426 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___107_3457 = env in
            let uu____3458 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3458;
              subst = (uu___107_3457.subst);
              tc_const = (uu___107_3457.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3467  ->
                 match uu____3467 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___108_3475 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___108_3475.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___108_3475.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3476 =
            FStar_List.fold_left
              (fun uu____3485  ->
                 fun uu____3486  ->
                   match (uu____3485, uu____3486) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3514 = is_C c in
                       if uu____3514
                       then
                         let xw =
                           let uu____3519 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3519 in
                         let x =
                           let uu___109_3521 = bv in
                           let uu____3522 =
                             let uu____3525 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3525 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___109_3521.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___109_3521.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3522
                           } in
                         let env3 =
                           let uu___110_3527 = env2 in
                           let uu____3528 =
                             let uu____3530 =
                               let uu____3531 =
                                 let uu____3536 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3536) in
                               FStar_Syntax_Syntax.NT uu____3531 in
                             uu____3530 :: (env2.subst) in
                           {
                             env = (uu___110_3527.env);
                             subst = uu____3528;
                             tc_const = (uu___110_3527.tc_const)
                           } in
                         let uu____3537 =
                           let uu____3539 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3540 =
                             let uu____3542 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3542 :: acc in
                           uu____3539 :: uu____3540 in
                         (env3, uu____3537)
                       else
                         (let x =
                            let uu___111_3546 = bv in
                            let uu____3547 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___111_3546.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___111_3546.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3547
                            } in
                          let uu____3550 =
                            let uu____3552 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3552 :: acc in
                          (env2, uu____3550))) (env1, []) binders1 in
          (match uu____3476 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3564 =
                 let check_what =
                   let uu____3576 = is_monadic what in
                   if uu____3576 then check_m else check_n in
                 let uu____3585 = check_what env2 body1 in
                 match uu____3585 with
                 | (t,s_body,u_body) ->
                     let uu____3595 =
                       let uu____3596 =
                         let uu____3597 = is_monadic what in
                         if uu____3597 then M t else N t in
                       comp_of_nm uu____3596 in
                     (uu____3595, s_body, u_body) in
               (match uu____3564 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some
                          { FStar_Syntax_Syntax.residual_effect = uu____3611;
                            FStar_Syntax_Syntax.residual_typ = None ;
                            FStar_Syntax_Syntax.residual_flags = uu____3612;_}
                          -> None
                      | Some rc ->
                          let rt =
                            FStar_Util.must
                              rc.FStar_Syntax_Syntax.residual_typ in
                          let uu____3622 =
                            FStar_All.pipe_right
                              rc.FStar_Syntax_Syntax.residual_flags
                              (FStar_Util.for_some
                                 (fun uu___95_3624  ->
                                    match uu___95_3624 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3625 -> false)) in
                          if uu____3622
                          then
                            let double_starred_comp =
                              let uu____3628 = double_star rt in
                              FStar_Syntax_Syntax.mk_Total uu____3628 in
                            let flags =
                              FStar_List.filter
                                (fun uu___96_3631  ->
                                   match uu___96_3631 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3632 -> true)
                                rc.FStar_Syntax_Syntax.residual_flags in
                            let uu____3633 =
                              let uu____3634 =
                                let uu____3635 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____3635 in
                              FStar_Syntax_Util.residual_comp_of_lcomp
                                uu____3634 in
                            Some uu____3633
                          else
                            (let uu____3639 =
                               let uu___112_3640 = rc in
                               let uu____3641 =
                                 let uu____3645 = star_type' env2 rt in
                                 Some uu____3645 in
                               {
                                 FStar_Syntax_Syntax.residual_effect =
                                   (uu___112_3640.FStar_Syntax_Syntax.residual_effect);
                                 FStar_Syntax_Syntax.residual_typ =
                                   uu____3641;
                                 FStar_Syntax_Syntax.residual_flags =
                                   (uu___112_3640.FStar_Syntax_Syntax.residual_flags)
                               } in
                             Some uu____3639) in
                    let uu____3646 =
                      let comp1 =
                        let uu____3653 = is_monadic what in
                        let uu____3654 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3653 uu____3654 in
                      let uu____3655 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____3655,
                        (Some (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____3646 with
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
                FStar_Syntax_Syntax.ty = uu____3700;
                FStar_Syntax_Syntax.p = uu____3701;_};
            FStar_Syntax_Syntax.fv_delta = uu____3702;
            FStar_Syntax_Syntax.fv_qual = uu____3703;_}
          ->
          let uu____3709 =
            let uu____3712 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____3712 in
          (match uu____3709 with
           | (uu____3728,t) ->
               let uu____3730 = let uu____3731 = normalize1 t in N uu____3731 in
               (uu____3730, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3748 = check_n env head1 in
          (match uu____3748 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3762 =
                   let uu____3763 = FStar_Syntax_Subst.compress t in
                   uu____3763.FStar_Syntax_Syntax.n in
                 match uu____3762 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3766 -> true
                 | uu____3774 -> false in
               let rec flatten1 t =
                 let uu____3786 =
                   let uu____3787 = FStar_Syntax_Subst.compress t in
                   uu____3787.FStar_Syntax_Syntax.n in
                 match uu____3786 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____3799);
                                FStar_Syntax_Syntax.tk = uu____3800;
                                FStar_Syntax_Syntax.pos = uu____3801;
                                FStar_Syntax_Syntax.vars = uu____3802;_})
                     when is_arrow t1 ->
                     let uu____3819 = flatten1 t1 in
                     (match uu____3819 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3871,uu____3872)
                     -> flatten1 e1
                 | uu____3901 ->
                     let uu____3902 =
                       let uu____3903 =
                         let uu____3904 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____3904 in
                       FStar_Errors.Err uu____3903 in
                     raise uu____3902 in
               let uu____3912 = flatten1 t_head in
               (match uu____3912 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____3957 =
                          let uu____3958 =
                            let uu____3959 = FStar_Util.string_of_int n1 in
                            let uu____3963 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____3969 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____3959 uu____3963 uu____3969 in
                          FStar_Errors.Err uu____3958 in
                        raise uu____3957)
                     else ();
                     (let uu____3974 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____3974 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4001 args1 =
                            match uu____4001 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4044 =
                                       let uu____4045 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4045.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4044
                                 | (binders3,[]) ->
                                     let uu____4064 =
                                       let uu____4065 =
                                         let uu____4068 =
                                           let uu____4069 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4069 in
                                         FStar_Syntax_Subst.compress
                                           uu____4068 in
                                       uu____4065.FStar_Syntax_Syntax.n in
                                     (match uu____4064 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4085 =
                                            let uu____4086 =
                                              let uu____4087 =
                                                let uu____4095 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4095) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4087 in
                                            mk1 uu____4086 in
                                          N uu____4085
                                      | uu____4099 -> failwith "wat?")
                                 | ([],uu____4100::uu____4101) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4126)::binders3,(arg,uu____4129)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4163 = FStar_List.splitAt n' binders1 in
                          (match uu____4163 with
                           | (binders2,uu____4180) ->
                               let uu____4193 =
                                 let uu____4203 =
                                   FStar_List.map2
                                     (fun uu____4223  ->
                                        fun uu____4224  ->
                                          match (uu____4223, uu____4224) with
                                          | ((bv,uu____4241),(arg,q)) ->
                                              let uu____4248 =
                                                let uu____4249 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4249.FStar_Syntax_Syntax.n in
                                              (match uu____4248 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4259 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4272 ->
                                                   let uu____4273 =
                                                     check_n env arg in
                                                   (match uu____4273 with
                                                    | (uu____4284,s_arg,u_arg)
                                                        ->
                                                        let uu____4287 =
                                                          let uu____4291 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4291
                                                          then
                                                            let uu____4295 =
                                                              let uu____4298
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4298, q) in
                                                            [uu____4295;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4287))))
                                     binders2 args in
                                 FStar_List.split uu____4203 in
                               (match uu____4193 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4345 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4351 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4345, uu____4351)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4400) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4406) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4412,uu____4413) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4443 = let uu____4444 = env.tc_const c in N uu____4444 in
          (uu____4443, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4445 ->
          let uu____4453 =
            let uu____4454 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4454 in
          failwith uu____4453
      | FStar_Syntax_Syntax.Tm_type uu____4458 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4462 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4473 ->
          let uu____4478 =
            let uu____4479 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4479 in
          failwith uu____4478
      | FStar_Syntax_Syntax.Tm_uvar uu____4483 ->
          let uu____4492 =
            let uu____4493 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4493 in
          failwith uu____4492
      | FStar_Syntax_Syntax.Tm_delayed uu____4497 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4515 =
            let uu____4516 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4516 in
          failwith uu____4515
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
          let uu____4554 = check_n env e0 in
          match uu____4554 with
          | (uu____4561,s_e0,u_e0) ->
              let uu____4564 =
                let uu____4582 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4615 = FStar_Syntax_Subst.open_branch b in
                       match uu____4615 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___113_4647 = env in
                             let uu____4648 =
                               let uu____4649 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4649 in
                             {
                               env = uu____4648;
                               subst = (uu___113_4647.subst);
                               tc_const = (uu___113_4647.tc_const)
                             } in
                           let uu____4651 = f env1 body in
                           (match uu____4651 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4700 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4582 in
              (match uu____4564 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____4765 = FStar_List.hd nms in
                     match uu____4765 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___97_4769  ->
                          match uu___97_4769 with
                          | M uu____4770 -> true
                          | uu____4771 -> false) nms in
                   let uu____4772 =
                     let uu____4795 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____4847  ->
                              match uu____4847 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____4970 =
                                         check env original_body (M t2) in
                                       (match uu____4970 with
                                        | (uu____4993,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5022,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____4795 in
                   (match uu____4772 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5141  ->
                                 match uu____5141 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5182 =
                                         let uu____5183 =
                                           let uu____5193 =
                                             let uu____5197 =
                                               let uu____5200 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5201 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5200, uu____5201) in
                                             [uu____5197] in
                                           (s_body, uu____5193) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5183 in
                                       mk1 uu____5182 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5223 =
                              let uu____5224 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5224] in
                            let uu____5225 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____5223 uu____5225
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____5230 =
                              let uu____5234 =
                                let uu____5235 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5235 in
                              [uu____5234] in
                            let uu____5236 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5230 uu____5236 in
                          let uu____5239 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5269 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5239, uu____5269)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5283 =
                             let uu____5286 =
                               let uu____5287 =
                                 let uu____5305 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5305,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5287 in
                             mk1 uu____5286 in
                           let uu____5332 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5283, uu____5332))))
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
              let uu____5375 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5375] in
            let uu____5376 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5376 with
            | (x_binders1,e21) ->
                let uu____5384 = infer env e1 in
                (match uu____5384 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5395 = is_C t1 in
                       if uu____5395
                       then
                         let uu___114_5396 = binding in
                         let uu____5397 =
                           let uu____5400 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5400 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___114_5396.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___114_5396.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5397;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___114_5396.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___114_5396.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___115_5403 = env in
                       let uu____5404 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___116_5405 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_5405.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_5405.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5404;
                         subst = (uu___115_5403.subst);
                         tc_const = (uu___115_5403.tc_const)
                       } in
                     let uu____5406 = proceed env1 e21 in
                     (match uu____5406 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___117_5417 = binding in
                            let uu____5418 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___117_5417.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___117_5417.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5418;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___117_5417.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___117_5417.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5421 =
                            let uu____5424 =
                              let uu____5425 =
                                let uu____5433 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___118_5438 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___118_5438.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___118_5438.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___118_5438.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___118_5438.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5433) in
                              FStar_Syntax_Syntax.Tm_let uu____5425 in
                            mk1 uu____5424 in
                          let uu____5439 =
                            let uu____5442 =
                              let uu____5443 =
                                let uu____5451 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___119_5456 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___119_5456.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___119_5456.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___119_5456.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___119_5456.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5451) in
                              FStar_Syntax_Syntax.Tm_let uu____5443 in
                            mk1 uu____5442 in
                          (nm_rec, uu____5421, uu____5439))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___120_5465 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___120_5465.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___120_5465.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___120_5465.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___121_5467 = env in
                       let uu____5468 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___122_5469 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_5469.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_5469.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5468;
                         subst = (uu___121_5467.subst);
                         tc_const = (uu___121_5467.tc_const)
                       } in
                     let uu____5470 = ensure_m env1 e21 in
                     (match uu____5470 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5487 =
                              let uu____5488 =
                                let uu____5498 =
                                  let uu____5502 =
                                    let uu____5505 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5506 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5505, uu____5506) in
                                  [uu____5502] in
                                (s_e2, uu____5498) in
                              FStar_Syntax_Syntax.Tm_app uu____5488 in
                            mk1 uu____5487 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____5518 =
                              let uu____5519 =
                                let uu____5529 =
                                  let uu____5533 =
                                    let uu____5536 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5536) in
                                  [uu____5533] in
                                (s_e1, uu____5529) in
                              FStar_Syntax_Syntax.Tm_app uu____5519 in
                            mk1 uu____5518 in
                          let uu____5544 =
                            let uu____5545 =
                              let uu____5546 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5546] in
                            FStar_Syntax_Util.abs uu____5545 body
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____5547 =
                            let uu____5550 =
                              let uu____5551 =
                                let uu____5559 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___123_5564 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_5564.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_5564.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_5564.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_5564.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5559) in
                              FStar_Syntax_Syntax.Tm_let uu____5551 in
                            mk1 uu____5550 in
                          ((M t2), uu____5544, uu____5547)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5573 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____5573 in
      let uu____5578 = check env e mn in
      match uu____5578 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5588 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5601 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____5601 in
      let uu____5606 = check env e mn in
      match uu____5606 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5616 -> failwith "[check_m]: impossible"
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
        (let uu____5638 =
           let uu____5639 = is_C c in Prims.op_Negation uu____5639 in
         if uu____5638 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____5651 =
           let uu____5652 = FStar_Syntax_Subst.compress c in
           uu____5652.FStar_Syntax_Syntax.n in
         match uu____5651 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5671 = FStar_Syntax_Util.head_and_args wp in
             (match uu____5671 with
              | (wp_head,wp_args) ->
                  ((let uu____5698 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5711 =
                           let uu____5712 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5712 in
                         Prims.op_Negation uu____5711) in
                    if uu____5698 then failwith "mismatch" else ());
                   (let uu____5721 =
                      let uu____5722 =
                        let uu____5732 =
                          FStar_List.map2
                            (fun uu____5742  ->
                               fun uu____5743  ->
                                 match (uu____5742, uu____5743) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____5766 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____5766
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____5769 = print_implicit q in
                                         let uu____5770 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____5769 uu____5770)
                                      else ();
                                      (let uu____5772 =
                                         trans_F_ env arg wp_arg in
                                       (uu____5772, q)))) args wp_args in
                        (head1, uu____5732) in
                      FStar_Syntax_Syntax.Tm_app uu____5722 in
                    mk1 uu____5721)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____5794 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____5794 with
              | (binders_orig,comp1) ->
                  let uu____5799 =
                    let uu____5807 =
                      FStar_List.map
                        (fun uu____5821  ->
                           match uu____5821 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____5834 = is_C h in
                               if uu____5834
                               then
                                 let w' =
                                   let uu____5841 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____5841 in
                                 let uu____5842 =
                                   let uu____5846 =
                                     let uu____5850 =
                                       let uu____5853 =
                                         let uu____5854 =
                                           let uu____5855 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____5855 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____5854 in
                                       (uu____5853, q) in
                                     [uu____5850] in
                                   (w', q) :: uu____5846 in
                                 (w', uu____5842)
                               else
                                 (let x =
                                    let uu____5867 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____5867 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____5807 in
                  (match uu____5799 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____5897 =
                           let uu____5899 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____5899 in
                         FStar_Syntax_Subst.subst_comp uu____5897 comp1 in
                       let app =
                         let uu____5903 =
                           let uu____5904 =
                             let uu____5914 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____5921 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____5922 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5921, uu____5922)) bvs in
                             (wp, uu____5914) in
                           FStar_Syntax_Syntax.Tm_app uu____5904 in
                         mk1 uu____5903 in
                       let comp3 =
                         let uu____5927 = type_of_comp comp2 in
                         let uu____5928 = is_monadic_comp comp2 in
                         trans_G env uu____5927 uu____5928 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____5930,uu____5931) ->
             trans_F_ env e wp
         | uu____5960 -> failwith "impossible trans_F_")
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
            let uu____5965 =
              let uu____5966 = star_type' env h in
              let uu____5969 =
                let uu____5975 =
                  let uu____5978 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____5978) in
                [uu____5975] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____5966;
                FStar_Syntax_Syntax.effect_args = uu____5969;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____5965
          else
            (let uu____5984 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____5984)
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
    fun t  -> let uu____5995 = n env.env t in star_type' env uu____5995
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6007 = n env.env t in check_n env uu____6007
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6017 = n env.env c in
        let uu____6018 = n env.env wp in trans_F_ env uu____6017 uu____6018