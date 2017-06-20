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
                FStar_Syntax_Syntax.mk x None FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____186 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____186 with
                | (sigelt,fv) ->
                    ((let uu____192 =
                        let uu____194 = FStar_ST.read sigelts in sigelt ::
                          uu____194 in
                      FStar_ST.write sigelts uu____192);
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
                     let uu____245 = FStar_Syntax_Syntax.as_implicit true in
                     ((fst t), uu____245)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____260 = FStar_Syntax_Syntax.bv_to_name (fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____260) in
              let uu____261 =
                let uu____273 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let body =
                      let uu____293 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____293 in
                    let uu____296 =
                      let uu____297 =
                        let uu____301 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____302 =
                          let uu____304 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____304] in
                        uu____301 :: uu____302 in
                      FStar_List.append binders uu____297 in
                    FStar_Syntax_Util.abs uu____296 body None in
                  let uu____312 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____313 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____312, uu____313) in
                match uu____273 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____344 =
                        let uu____345 =
                          let uu____355 =
                            let uu____359 =
                              FStar_List.map
                                (fun uu____372  ->
                                   match uu____372 with
                                   | (bv,uu____378) ->
                                       let uu____379 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____380 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____379, uu____380)) binders in
                            let uu____381 =
                              let uu____385 =
                                let uu____388 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____389 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____388, uu____389) in
                              let uu____390 =
                                let uu____394 =
                                  let uu____397 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____397) in
                                [uu____394] in
                              uu____385 :: uu____390 in
                            FStar_List.append uu____359 uu____381 in
                          (fv, uu____355) in
                        FStar_Syntax_Syntax.Tm_app uu____345 in
                      mk1 uu____344 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____261 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____443 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____443 in
                    let ret1 =
                      let uu____451 =
                        let uu____457 =
                          let uu____458 =
                            let uu____461 =
                              let uu____462 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____462 in
                            FStar_Syntax_Syntax.mk_Total uu____461 in
                          FStar_Syntax_Util.lcomp_of_comp uu____458 in
                        FStar_Util.Inl uu____457 in
                      Some uu____451 in
                    let body =
                      let uu____472 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____472 ret1 in
                    let uu____473 =
                      let uu____474 = mk_all_implicit binders in
                      let uu____478 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____474 uu____478 in
                    FStar_Syntax_Util.abs uu____473 body ret1 in
                  let c_pure1 =
                    let uu____493 = mk_lid "pure" in
                    register env1 uu____493 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____498 =
                        let uu____499 =
                          let uu____500 =
                            let uu____504 =
                              let uu____505 =
                                let uu____506 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____506 in
                              FStar_Syntax_Syntax.mk_binder uu____505 in
                            [uu____504] in
                          let uu____507 =
                            let uu____510 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____510 in
                          FStar_Syntax_Util.arrow uu____500 uu____507 in
                        mk_gctx uu____499 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____498 in
                    let r =
                      let uu____512 =
                        let uu____513 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____513 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____512 in
                    let ret1 =
                      let uu____521 =
                        let uu____527 =
                          let uu____528 =
                            let uu____531 =
                              let uu____532 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____532 in
                            FStar_Syntax_Syntax.mk_Total uu____531 in
                          FStar_Syntax_Util.lcomp_of_comp uu____528 in
                        FStar_Util.Inl uu____527 in
                      Some uu____521 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____547 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____550 =
                          let uu____556 =
                            let uu____558 =
                              let uu____559 =
                                let uu____560 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____560
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____559 in
                            [uu____558] in
                          FStar_List.append gamma_as_args uu____556 in
                        FStar_Syntax_Util.mk_app uu____547 uu____550 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____563 =
                      let uu____564 = mk_all_implicit binders in
                      let uu____568 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____564 uu____568 in
                    FStar_Syntax_Util.abs uu____563 outer_body ret1 in
                  let c_app1 =
                    let uu____587 = mk_lid "app" in
                    register env1 uu____587 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____594 =
                        let uu____598 =
                          let uu____599 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____599 in
                        [uu____598] in
                      let uu____600 =
                        let uu____603 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____603 in
                      FStar_Syntax_Util.arrow uu____594 uu____600 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____606 =
                        let uu____607 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____607 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____606 in
                    let ret1 =
                      let uu____615 =
                        let uu____621 =
                          let uu____622 =
                            let uu____625 =
                              let uu____626 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____626 in
                            FStar_Syntax_Syntax.mk_Total uu____625 in
                          FStar_Syntax_Util.lcomp_of_comp uu____622 in
                        FStar_Util.Inl uu____621 in
                      Some uu____615 in
                    let uu____635 =
                      let uu____636 = mk_all_implicit binders in
                      let uu____640 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____636 uu____640 in
                    let uu____658 =
                      let uu____659 =
                        let uu____665 =
                          let uu____667 =
                            let uu____670 =
                              let uu____676 =
                                let uu____678 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____678] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____676 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____670 in
                          let uu____679 =
                            let uu____683 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____683] in
                          uu____667 :: uu____679 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____665 in
                      FStar_Syntax_Util.mk_app c_app1 uu____659 in
                    FStar_Syntax_Util.abs uu____635 uu____658 ret1 in
                  let c_lift11 =
                    let uu____687 = mk_lid "lift1" in
                    register env1 uu____687 c_lift1 in
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
                      let uu____695 =
                        let uu____699 =
                          let uu____700 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____700 in
                        let uu____701 =
                          let uu____703 =
                            let uu____704 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____704 in
                          [uu____703] in
                        uu____699 :: uu____701 in
                      let uu____705 =
                        let uu____708 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____708 in
                      FStar_Syntax_Util.arrow uu____695 uu____705 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____711 =
                        let uu____712 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____712 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____711 in
                    let a2 =
                      let uu____714 =
                        let uu____715 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____715 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____714 in
                    let ret1 =
                      let uu____723 =
                        let uu____729 =
                          let uu____730 =
                            let uu____733 =
                              let uu____734 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____734 in
                            FStar_Syntax_Syntax.mk_Total uu____733 in
                          FStar_Syntax_Util.lcomp_of_comp uu____730 in
                        FStar_Util.Inl uu____729 in
                      Some uu____723 in
                    let uu____743 =
                      let uu____744 = mk_all_implicit binders in
                      let uu____748 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____744 uu____748 in
                    let uu____770 =
                      let uu____771 =
                        let uu____777 =
                          let uu____779 =
                            let uu____782 =
                              let uu____788 =
                                let uu____790 =
                                  let uu____793 =
                                    let uu____799 =
                                      let uu____801 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____801] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____799 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____793 in
                                let uu____802 =
                                  let uu____806 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____806] in
                                uu____790 :: uu____802 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____788 in
                            FStar_Syntax_Util.mk_app c_app1 uu____782 in
                          let uu____809 =
                            let uu____813 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____813] in
                          uu____779 :: uu____809 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____777 in
                      FStar_Syntax_Util.mk_app c_app1 uu____771 in
                    FStar_Syntax_Util.abs uu____743 uu____770 ret1 in
                  let c_lift21 =
                    let uu____817 = mk_lid "lift2" in
                    register env1 uu____817 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____824 =
                        let uu____828 =
                          let uu____829 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____829 in
                        [uu____828] in
                      let uu____830 =
                        let uu____833 =
                          let uu____834 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____834 in
                        FStar_Syntax_Syntax.mk_Total uu____833 in
                      FStar_Syntax_Util.arrow uu____824 uu____830 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____843 =
                        let uu____849 =
                          let uu____850 =
                            let uu____853 =
                              let uu____854 =
                                let uu____855 =
                                  let uu____859 =
                                    let uu____860 =
                                      FStar_Syntax_Syntax.bv_to_name t1 in
                                    FStar_Syntax_Syntax.null_binder uu____860 in
                                  [uu____859] in
                                let uu____861 =
                                  let uu____864 =
                                    FStar_Syntax_Syntax.bv_to_name t2 in
                                  FStar_Syntax_Syntax.mk_GTotal uu____864 in
                                FStar_Syntax_Util.arrow uu____855 uu____861 in
                              mk_ctx uu____854 in
                            FStar_Syntax_Syntax.mk_Total uu____853 in
                          FStar_Syntax_Util.lcomp_of_comp uu____850 in
                        FStar_Util.Inl uu____849 in
                      Some uu____843 in
                    let e1 =
                      let uu____874 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____874 in
                    let body =
                      let uu____876 =
                        let uu____877 =
                          let uu____881 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____881] in
                        FStar_List.append gamma uu____877 in
                      let uu____884 =
                        let uu____885 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____888 =
                          let uu____894 =
                            let uu____895 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____895 in
                          let uu____896 = args_of_binders1 gamma in uu____894
                            :: uu____896 in
                        FStar_Syntax_Util.mk_app uu____885 uu____888 in
                      FStar_Syntax_Util.abs uu____876 uu____884 ret1 in
                    let uu____898 =
                      let uu____899 = mk_all_implicit binders in
                      let uu____903 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____899 uu____903 in
                    FStar_Syntax_Util.abs uu____898 body ret1 in
                  let c_push1 =
                    let uu____920 = mk_lid "push" in
                    register env1 uu____920 c_push in
                  let ret_tot_wp_a =
                    let uu____928 =
                      let uu____934 =
                        let uu____935 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____935 in
                      FStar_Util.Inl uu____934 in
                    Some uu____928 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____963 =
                        let uu____964 =
                          let uu____974 = args_of_binders1 binders in
                          (c, uu____974) in
                        FStar_Syntax_Syntax.Tm_app uu____964 in
                      mk1 uu____963
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____982 =
                        let uu____983 =
                          let uu____987 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____988 =
                            let uu____990 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____990] in
                          uu____987 :: uu____988 in
                        let uu____991 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____983 uu____991 in
                      FStar_Syntax_Syntax.mk_Total uu____982 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____995 =
                      let uu____996 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____996 in
                    let uu____1002 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____1004 =
                        let uu____1007 =
                          let uu____1013 =
                            let uu____1015 =
                              let uu____1018 =
                                let uu____1024 =
                                  let uu____1025 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1025 in
                                [uu____1024] in
                              FStar_Syntax_Util.mk_app l_ite uu____1018 in
                            [uu____1015] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1013 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1007 in
                      FStar_Syntax_Util.ascribe uu____1004
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____995 uu____1002
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1050 = mk_lid "wp_if_then_else" in
                    register env1 uu____1050 wp_if_then_else in
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
                      let uu____1061 =
                        let uu____1067 =
                          let uu____1069 =
                            let uu____1072 =
                              let uu____1078 =
                                let uu____1080 =
                                  let uu____1083 =
                                    let uu____1089 =
                                      let uu____1090 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1090 in
                                    [uu____1089] in
                                  FStar_Syntax_Util.mk_app l_and uu____1083 in
                                [uu____1080] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1078 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1072 in
                          let uu____1095 =
                            let uu____1099 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1099] in
                          uu____1069 :: uu____1095 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1067 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1061 in
                    let uu____1102 =
                      let uu____1103 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1103 in
                    FStar_Syntax_Util.abs uu____1102 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1110 = mk_lid "wp_assert" in
                    register env1 uu____1110 wp_assert in
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
                      let uu____1121 =
                        let uu____1127 =
                          let uu____1129 =
                            let uu____1132 =
                              let uu____1138 =
                                let uu____1140 =
                                  let uu____1143 =
                                    let uu____1149 =
                                      let uu____1150 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1150 in
                                    [uu____1149] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1143 in
                                [uu____1140] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1138 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1132 in
                          let uu____1155 =
                            let uu____1159 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1159] in
                          uu____1129 :: uu____1155 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1127 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1121 in
                    let uu____1162 =
                      let uu____1163 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1163 in
                    FStar_Syntax_Util.abs uu____1162 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1170 = mk_lid "wp_assume" in
                    register env1 uu____1170 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1179 =
                        let uu____1183 =
                          let uu____1184 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1184 in
                        [uu____1183] in
                      let uu____1185 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1179 uu____1185 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1192 =
                        let uu____1198 =
                          let uu____1200 =
                            let uu____1203 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1203 in
                          let uu____1209 =
                            let uu____1213 =
                              let uu____1216 =
                                let uu____1222 =
                                  let uu____1224 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1224] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1222 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1216 in
                            [uu____1213] in
                          uu____1200 :: uu____1209 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1198 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1192 in
                    let uu____1231 =
                      let uu____1232 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1232 in
                    FStar_Syntax_Util.abs uu____1231 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1239 = mk_lid "wp_close" in
                    register env1 uu____1239 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1250 =
                      let uu____1256 =
                        let uu____1257 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1257 in
                      FStar_Util.Inl uu____1256 in
                    Some uu____1250 in
                  let ret_gtot_type =
                    let uu____1277 =
                      let uu____1283 =
                        let uu____1284 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1284 in
                      FStar_Util.Inl uu____1283 in
                    Some uu____1277 in
                  let mk_forall1 x body =
                    let uu____1304 =
                      let uu____1307 =
                        let uu____1308 =
                          let uu____1318 =
                            let uu____1320 =
                              let uu____1321 =
                                let uu____1322 =
                                  let uu____1323 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1323] in
                                FStar_Syntax_Util.abs uu____1322 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1321 in
                            [uu____1320] in
                          (FStar_Syntax_Util.tforall, uu____1318) in
                        FStar_Syntax_Syntax.Tm_app uu____1308 in
                      FStar_Syntax_Syntax.mk uu____1307 in
                    uu____1304 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1337 =
                      let uu____1338 = FStar_Syntax_Subst.compress t in
                      uu____1338.FStar_Syntax_Syntax.n in
                    match uu____1337 with
                    | FStar_Syntax_Syntax.Tm_type uu____1341 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1359  ->
                              match uu____1359 with
                              | (b,uu____1363) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1364 -> true in
                  let rec is_monotonic t =
                    let uu____1369 =
                      let uu____1370 = FStar_Syntax_Subst.compress t in
                      uu____1370.FStar_Syntax_Syntax.n in
                    match uu____1369 with
                    | FStar_Syntax_Syntax.Tm_type uu____1373 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1391  ->
                              match uu____1391 with
                              | (b,uu____1395) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1396 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1448 =
                      let uu____1449 = FStar_Syntax_Subst.compress t1 in
                      uu____1449.FStar_Syntax_Syntax.n in
                    match uu____1448 with
                    | FStar_Syntax_Syntax.Tm_type uu____1452 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1455);
                                      FStar_Syntax_Syntax.tk = uu____1456;
                                      FStar_Syntax_Syntax.pos = uu____1457;
                                      FStar_Syntax_Syntax.vars = uu____1458;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1481 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1481
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1484 =
                              let uu____1487 =
                                let uu____1493 =
                                  let uu____1494 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1494 in
                                [uu____1493] in
                              FStar_Syntax_Util.mk_app x uu____1487 in
                            let uu____1495 =
                              let uu____1498 =
                                let uu____1504 =
                                  let uu____1505 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1505 in
                                [uu____1504] in
                              FStar_Syntax_Util.mk_app y uu____1498 in
                            mk_rel1 b uu____1484 uu____1495 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1510 =
                               let uu____1511 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1514 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1511 uu____1514 in
                             let uu____1517 =
                               let uu____1518 =
                                 let uu____1521 =
                                   let uu____1527 =
                                     let uu____1528 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1528 in
                                   [uu____1527] in
                                 FStar_Syntax_Util.mk_app x uu____1521 in
                               let uu____1529 =
                                 let uu____1532 =
                                   let uu____1538 =
                                     let uu____1539 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1539 in
                                   [uu____1538] in
                                 FStar_Syntax_Util.mk_app y uu____1532 in
                               mk_rel1 b uu____1518 uu____1529 in
                             FStar_Syntax_Util.mk_imp uu____1510 uu____1517 in
                           let uu____1540 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1540)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1543);
                                      FStar_Syntax_Syntax.tk = uu____1544;
                                      FStar_Syntax_Syntax.pos = uu____1545;
                                      FStar_Syntax_Syntax.vars = uu____1546;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1569 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1569
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1572 =
                              let uu____1575 =
                                let uu____1581 =
                                  let uu____1582 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1582 in
                                [uu____1581] in
                              FStar_Syntax_Util.mk_app x uu____1575 in
                            let uu____1583 =
                              let uu____1586 =
                                let uu____1592 =
                                  let uu____1593 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1593 in
                                [uu____1592] in
                              FStar_Syntax_Util.mk_app y uu____1586 in
                            mk_rel1 b uu____1572 uu____1583 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1598 =
                               let uu____1599 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1602 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1599 uu____1602 in
                             let uu____1605 =
                               let uu____1606 =
                                 let uu____1609 =
                                   let uu____1615 =
                                     let uu____1616 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1616 in
                                   [uu____1615] in
                                 FStar_Syntax_Util.mk_app x uu____1609 in
                               let uu____1617 =
                                 let uu____1620 =
                                   let uu____1626 =
                                     let uu____1627 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1627 in
                                   [uu____1626] in
                                 FStar_Syntax_Util.mk_app y uu____1620 in
                               mk_rel1 b uu____1606 uu____1617 in
                             FStar_Syntax_Util.mk_imp uu____1598 uu____1605 in
                           let uu____1628 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1628)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___101_1649 = t1 in
                          let uu____1650 =
                            let uu____1651 =
                              let uu____1659 =
                                let uu____1660 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1660 in
                              ([binder], uu____1659) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1651 in
                          {
                            FStar_Syntax_Syntax.n = uu____1650;
                            FStar_Syntax_Syntax.tk =
                              (uu___101_1649.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___101_1649.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___101_1649.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1672 ->
                        failwith "unhandled arrow"
                    | uu____1680 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1695 =
                        let uu____1696 = FStar_Syntax_Subst.compress t1 in
                        uu____1696.FStar_Syntax_Syntax.n in
                      match uu____1695 with
                      | FStar_Syntax_Syntax.Tm_type uu____1699 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1716 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1716
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1731 =
                                let uu____1732 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1732 i in
                              FStar_Syntax_Syntax.fvar uu____1731
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1753 =
                            let uu____1757 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1768  ->
                                     match uu____1768 with
                                     | (t2,q) ->
                                         let uu____1773 = project i x in
                                         let uu____1774 = project i y in
                                         mk_stronger t2 uu____1773 uu____1774)
                                args in
                            match uu____1757 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1753 with
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
                                 fun uu____1821  ->
                                   match uu____1821 with
                                   | (bv,q) ->
                                       let uu____1826 =
                                         let uu____1827 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1827 in
                                       FStar_Syntax_Syntax.gen_bv uu____1826
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1833 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1833) bvs in
                          let body =
                            let uu____1835 = FStar_Syntax_Util.mk_app x args in
                            let uu____1836 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1835 uu____1836 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1843);
                                      FStar_Syntax_Syntax.tk = uu____1844;
                                      FStar_Syntax_Syntax.pos = uu____1845;
                                      FStar_Syntax_Syntax.vars = uu____1846;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1873  ->
                                   match uu____1873 with
                                   | (bv,q) ->
                                       let uu____1878 =
                                         let uu____1879 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1879 in
                                       FStar_Syntax_Syntax.gen_bv uu____1878
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1885 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1885) bvs in
                          let body =
                            let uu____1887 = FStar_Syntax_Util.mk_app x args in
                            let uu____1888 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1887 uu____1888 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1893 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1895 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1896 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1897 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1895 uu____1896 uu____1897 in
                    let uu____1898 =
                      let uu____1899 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1899 in
                    FStar_Syntax_Util.abs uu____1898 body ret_tot_type in
                  let stronger1 =
                    let uu____1914 = mk_lid "stronger" in
                    register env1 uu____1914 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1920 = FStar_Util.prefix gamma in
                    match uu____1920 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1946 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1946 in
                          let uu____1949 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1949 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1957 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1957 in
                              let guard_free1 =
                                let uu____1964 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1964 in
                              let pat =
                                let uu____1968 =
                                  let uu____1974 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1974] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1968 in
                              let pattern_guarded_body =
                                let uu____1978 =
                                  let uu____1979 =
                                    let uu____1984 =
                                      let uu____1985 =
                                        let uu____1992 =
                                          let uu____1994 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1994] in
                                        [uu____1992] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1985 in
                                    (body, uu____1984) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1979 in
                                mk1 uu____1978 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1997 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2000 =
                            let uu____2001 =
                              let uu____2002 =
                                let uu____2003 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2006 =
                                  let uu____2012 = args_of_binders1 wp_args in
                                  let uu____2014 =
                                    let uu____2016 =
                                      let uu____2017 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2017 in
                                    [uu____2016] in
                                  FStar_List.append uu____2012 uu____2014 in
                                FStar_Syntax_Util.mk_app uu____2003
                                  uu____2006 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2002 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2001 in
                          FStar_Syntax_Util.abs gamma uu____2000
                            ret_gtot_type in
                        let uu____2018 =
                          let uu____2019 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2019 in
                        FStar_Syntax_Util.abs uu____2018 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2026 = mk_lid "wp_ite" in
                    register env1 uu____2026 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2032 = FStar_Util.prefix gamma in
                    match uu____2032 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2056 =
                            let uu____2057 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2060 =
                              let uu____2066 =
                                let uu____2067 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2067 in
                              [uu____2066] in
                            FStar_Syntax_Util.mk_app uu____2057 uu____2060 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2056 in
                        let uu____2068 =
                          let uu____2069 =
                            let uu____2073 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2073 gamma in
                          FStar_List.append binders uu____2069 in
                        FStar_Syntax_Util.abs uu____2068 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2082 = mk_lid "null_wp" in
                    register env1 uu____2082 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2091 =
                        let uu____2097 =
                          let uu____2099 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2100 =
                            let uu____2102 =
                              let uu____2105 =
                                let uu____2111 =
                                  let uu____2112 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2112 in
                                [uu____2111] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2105 in
                            let uu____2113 =
                              let uu____2117 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2117] in
                            uu____2102 :: uu____2113 in
                          uu____2099 :: uu____2100 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2097 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2091 in
                    let uu____2120 =
                      let uu____2121 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2121 in
                    FStar_Syntax_Util.abs uu____2120 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2128 = mk_lid "wp_trivial" in
                    register env1 uu____2128 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2133 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2133
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2138 =
                      let uu____2140 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2140 in
                    let uu____2145 =
                      let uu___102_2146 = ed in
                      let uu____2147 =
                        let uu____2148 = c wp_if_then_else2 in
                        ([], uu____2148) in
                      let uu____2150 =
                        let uu____2151 = c wp_ite2 in ([], uu____2151) in
                      let uu____2153 =
                        let uu____2154 = c stronger2 in ([], uu____2154) in
                      let uu____2156 =
                        let uu____2157 = c wp_close2 in ([], uu____2157) in
                      let uu____2159 =
                        let uu____2160 = c wp_assert2 in ([], uu____2160) in
                      let uu____2162 =
                        let uu____2163 = c wp_assume2 in ([], uu____2163) in
                      let uu____2165 =
                        let uu____2166 = c null_wp2 in ([], uu____2166) in
                      let uu____2168 =
                        let uu____2169 = c wp_trivial2 in ([], uu____2169) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___102_2146.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___102_2146.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___102_2146.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___102_2146.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___102_2146.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___102_2146.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___102_2146.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2147;
                        FStar_Syntax_Syntax.ite_wp = uu____2150;
                        FStar_Syntax_Syntax.stronger = uu____2153;
                        FStar_Syntax_Syntax.close_wp = uu____2156;
                        FStar_Syntax_Syntax.assert_p = uu____2159;
                        FStar_Syntax_Syntax.assume_p = uu____2162;
                        FStar_Syntax_Syntax.null_wp = uu____2165;
                        FStar_Syntax_Syntax.trivial = uu____2168;
                        FStar_Syntax_Syntax.repr =
                          (uu___102_2146.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___102_2146.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___102_2146.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___102_2146.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2138, uu____2145)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___103_2181 = dmff_env in
      {
        env = env';
        subst = (uu___103_2181.subst);
        tc_const = (uu___103_2181.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2194 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2206 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___89_2216  ->
    match uu___89_2216 with
    | FStar_Syntax_Syntax.Total (t,uu____2218) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___88_2228  ->
                match uu___88_2228 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2229 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2231 =
          let uu____2232 =
            let uu____2233 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2233 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2232 in
        failwith uu____2231
    | FStar_Syntax_Syntax.GTotal uu____2234 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___90_2242  ->
    match uu___90_2242 with
    | N t ->
        let uu____2244 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2244
    | M t ->
        let uu____2246 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2246
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2250,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2252;
                      FStar_Syntax_Syntax.pos = uu____2253;
                      FStar_Syntax_Syntax.vars = uu____2254;_})
        -> nm_of_comp n2
    | uu____2265 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2277 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2277 with | M uu____2278 -> true | N uu____2279 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2283 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2293 =
        let uu____2297 =
          let uu____2298 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2298 in
        [uu____2297] in
      let uu____2299 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2293 uu____2299 in
    let uu____2302 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2302
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
          (let uu____2339 =
             let uu____2347 =
               let uu____2351 =
                 let uu____2354 =
                   let uu____2355 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2355 in
                 let uu____2356 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2354, uu____2356) in
               [uu____2351] in
             let uu____2361 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2347, uu____2361) in
           FStar_Syntax_Syntax.Tm_arrow uu____2339)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2390) ->
          let binders1 =
            FStar_List.map
              (fun uu____2413  ->
                 match uu____2413 with
                 | (bv,aqual) ->
                     let uu____2420 =
                       let uu___104_2421 = bv in
                       let uu____2422 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___104_2421.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___104_2421.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2422
                       } in
                     (uu____2420, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2425,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2427);
                             FStar_Syntax_Syntax.tk = uu____2428;
                             FStar_Syntax_Syntax.pos = uu____2429;
                             FStar_Syntax_Syntax.vars = uu____2430;_})
               ->
               let uu____2447 =
                 let uu____2448 =
                   let uu____2456 =
                     let uu____2457 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2457 in
                   (binders1, uu____2456) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2448 in
               mk1 uu____2447
           | uu____2461 ->
               let uu____2462 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2462 with
                | N hn ->
                    let uu____2464 =
                      let uu____2465 =
                        let uu____2473 =
                          let uu____2474 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2474 in
                        (binders1, uu____2473) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2465 in
                    mk1 uu____2464
                | M a ->
                    let uu____2479 =
                      let uu____2480 =
                        let uu____2488 =
                          let uu____2492 =
                            let uu____2496 =
                              let uu____2499 =
                                let uu____2500 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2500 in
                              let uu____2501 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2499, uu____2501) in
                            [uu____2496] in
                          FStar_List.append binders1 uu____2492 in
                        let uu____2508 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2488, uu____2508) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2480 in
                    mk1 uu____2479))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2559 = f x in
                    FStar_Util.string_builder_append strb uu____2559);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2566 = f x1 in
                         FStar_Util.string_builder_append strb uu____2566))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2568 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2569 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2568 uu____2569 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2577 =
              let uu____2578 = FStar_Syntax_Subst.compress ty in
              uu____2578.FStar_Syntax_Syntax.n in
            match uu____2577 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2593 =
                  let uu____2594 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2594 in
                if uu____2593
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2617 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2617 s in
                       let uu____2619 =
                         let uu____2620 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2620 in
                       if uu____2619
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2623 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2623 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2639  ->
                                  match uu____2639 with
                                  | (bv,uu____2645) ->
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
                  (let uu____2672 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2672)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____2674 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____2674 with
                 | ((uu____2679,ty),uu____2681) ->
                     let uu____2684 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____2684
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____2692 -> true
                        | uu____2702 ->
                            ((let uu____2704 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____2704);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____2706 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2707 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2709) ->
                is_valid_application t2
            | uu____2714 -> false in
          let uu____2715 = is_valid_application head1 in
          if uu____2715
          then
            let uu____2716 =
              let uu____2717 =
                let uu____2727 =
                  FStar_List.map
                    (fun uu____2741  ->
                       match uu____2741 with
                       | (t2,qual) ->
                           let uu____2754 = star_type' env t2 in
                           (uu____2754, qual)) args in
                (head1, uu____2727) in
              FStar_Syntax_Syntax.Tm_app uu____2717 in
            mk1 uu____2716
          else
            (let uu____2761 =
               let uu____2762 =
                 let uu____2763 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2763 in
               FStar_Errors.Err uu____2762 in
             raise uu____2761)
      | FStar_Syntax_Syntax.Tm_bvar uu____2764 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2765 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2766 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2767 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2793 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2793 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___107_2799 = env in
                 let uu____2800 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2800;
                   subst = (uu___107_2799.subst);
                   tc_const = (uu___107_2799.tc_const)
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
               ((let uu___108_2818 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___108_2818.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___108_2818.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2825 =
            let uu____2826 =
              let uu____2831 = star_type' env t2 in (uu____2831, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2826 in
          mk1 uu____2825
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2869 =
            let uu____2870 =
              let uu____2888 = star_type' env e in
              let uu____2889 =
                let uu____2899 =
                  let uu____2904 = star_type' env t2 in
                  FStar_Util.Inl uu____2904 in
                (uu____2899, None) in
              (uu____2888, uu____2889, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2870 in
          mk1 uu____2869
      | FStar_Syntax_Syntax.Tm_ascribed uu____2926 ->
          let uu____2944 =
            let uu____2945 =
              let uu____2946 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2946 in
            FStar_Errors.Err uu____2945 in
          raise uu____2944
      | FStar_Syntax_Syntax.Tm_refine uu____2947 ->
          let uu____2952 =
            let uu____2953 =
              let uu____2954 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2954 in
            FStar_Errors.Err uu____2953 in
          raise uu____2952
      | FStar_Syntax_Syntax.Tm_uinst uu____2955 ->
          let uu____2960 =
            let uu____2961 =
              let uu____2962 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2962 in
            FStar_Errors.Err uu____2961 in
          raise uu____2960
      | FStar_Syntax_Syntax.Tm_constant uu____2963 ->
          let uu____2964 =
            let uu____2965 =
              let uu____2966 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2966 in
            FStar_Errors.Err uu____2965 in
          raise uu____2964
      | FStar_Syntax_Syntax.Tm_match uu____2967 ->
          let uu____2982 =
            let uu____2983 =
              let uu____2984 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2984 in
            FStar_Errors.Err uu____2983 in
          raise uu____2982
      | FStar_Syntax_Syntax.Tm_let uu____2985 ->
          let uu____2993 =
            let uu____2994 =
              let uu____2995 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2995 in
            FStar_Errors.Err uu____2994 in
          raise uu____2993
      | FStar_Syntax_Syntax.Tm_uvar uu____2996 ->
          let uu____3007 =
            let uu____3008 =
              let uu____3009 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____3009 in
            FStar_Errors.Err uu____3008 in
          raise uu____3007
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____3010 =
            let uu____3011 =
              let uu____3012 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____3012 in
            FStar_Errors.Err uu____3011 in
          raise uu____3010
      | FStar_Syntax_Syntax.Tm_delayed uu____3013 -> failwith "impossible"
let is_monadic uu___92_3046 =
  match uu___92_3046 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3058;
        FStar_Syntax_Syntax.res_typ = uu____3059;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3061;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_3079  ->
              match uu___91_3079 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3080 -> false))
  | Some (FStar_Util.Inr (uu____3081,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_3095  ->
              match uu___91_3095 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3096 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3100 =
      let uu____3101 = FStar_Syntax_Subst.compress t in
      uu____3101.FStar_Syntax_Syntax.n in
    match uu____3100 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3121 =
            let uu____3122 = FStar_List.hd args in fst uu____3122 in
          is_C uu____3121 in
        if r
        then
          ((let uu____3134 =
              let uu____3135 =
                FStar_List.for_all
                  (fun uu____3141  ->
                     match uu____3141 with | (h,uu____3145) -> is_C h) args in
              Prims.op_Negation uu____3135 in
            if uu____3134 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3149 =
              let uu____3150 =
                FStar_List.for_all
                  (fun uu____3157  ->
                     match uu____3157 with
                     | (h,uu____3161) ->
                         let uu____3162 = is_C h in
                         Prims.op_Negation uu____3162) args in
              Prims.op_Negation uu____3150 in
            if uu____3149 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3176 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3176 with
         | M t1 ->
             ((let uu____3179 = is_C t1 in
               if uu____3179 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3183) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3189) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3195,uu____3196) -> is_C t1
    | uu____3225 -> false
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
          let uu____3252 =
            let uu____3253 =
              let uu____3263 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3264 =
                let uu____3268 =
                  let uu____3271 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3271) in
                [uu____3268] in
              (uu____3263, uu____3264) in
            FStar_Syntax_Syntax.Tm_app uu____3253 in
          mk1 uu____3252 in
        let uu____3279 =
          let uu____3280 = FStar_Syntax_Syntax.mk_binder p in [uu____3280] in
        let uu____3281 =
          let uu____3288 =
            let uu____3294 =
              let uu____3295 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3295 in
            FStar_Util.Inl uu____3294 in
          Some uu____3288 in
        FStar_Syntax_Util.abs uu____3279 body uu____3281
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___93_3308  ->
    match uu___93_3308 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3309 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3442 =
          match uu____3442 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3463 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3465 =
                       let uu____3466 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3466 in
                     Prims.op_Negation uu____3465) in
                if uu____3463
                then
                  let uu____3467 =
                    let uu____3468 =
                      let uu____3469 = FStar_Syntax_Print.term_to_string e in
                      let uu____3470 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3471 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3469 uu____3470 uu____3471 in
                    FStar_Errors.Err uu____3468 in
                  raise uu____3467
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3485 = mk_return env t1 s_e in
                     ((M t1), uu____3485, u_e)))
               | (M t1,N t2) ->
                   let uu____3488 =
                     let uu____3489 =
                       let uu____3490 = FStar_Syntax_Print.term_to_string e in
                       let uu____3491 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3492 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3490 uu____3491 uu____3492 in
                     FStar_Errors.Err uu____3489 in
                   raise uu____3488) in
        let ensure_m env1 e2 =
          let strip_m uu___94_3518 =
            match uu___94_3518 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3528 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3539 =
                let uu____3540 =
                  let uu____3543 =
                    let uu____3544 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3544 in
                  (uu____3543, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3540 in
              raise uu____3539
          | M uu____3548 ->
              let uu____3549 = check env1 e2 context_nm in strip_m uu____3549 in
        let uu____3553 =
          let uu____3554 = FStar_Syntax_Subst.compress e in
          uu____3554.FStar_Syntax_Syntax.n in
        match uu____3553 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3560 ->
            let uu____3561 = infer env e in return_if uu____3561
        | FStar_Syntax_Syntax.Tm_name uu____3565 ->
            let uu____3566 = infer env e in return_if uu____3566
        | FStar_Syntax_Syntax.Tm_fvar uu____3570 ->
            let uu____3571 = infer env e in return_if uu____3571
        | FStar_Syntax_Syntax.Tm_abs uu____3575 ->
            let uu____3590 = infer env e in return_if uu____3590
        | FStar_Syntax_Syntax.Tm_constant uu____3594 ->
            let uu____3595 = infer env e in return_if uu____3595
        | FStar_Syntax_Syntax.Tm_app uu____3599 ->
            let uu____3609 = infer env e in return_if uu____3609
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3658) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3664) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3670,uu____3671) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3700 ->
            let uu____3708 =
              let uu____3709 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3709 in
            failwith uu____3708
        | FStar_Syntax_Syntax.Tm_type uu____3713 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3717 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3728 ->
            let uu____3733 =
              let uu____3734 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3734 in
            failwith uu____3733
        | FStar_Syntax_Syntax.Tm_uvar uu____3738 ->
            let uu____3749 =
              let uu____3750 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3750 in
            failwith uu____3749
        | FStar_Syntax_Syntax.Tm_delayed uu____3754 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3778 =
              let uu____3779 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3779 in
            failwith uu____3778
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
      let uu____3801 =
        let uu____3802 = FStar_Syntax_Subst.compress e in
        uu____3802.FStar_Syntax_Syntax.n in
      match uu____3801 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___109_3842 = env in
            let uu____3843 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3843;
              subst = (uu___109_3842.subst);
              tc_const = (uu___109_3842.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3856  ->
                 match uu____3856 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___110_3865 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___110_3865.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___110_3865.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3866 =
            FStar_List.fold_left
              (fun uu____3887  ->
                 fun uu____3888  ->
                   match (uu____3887, uu____3888) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3916 = is_C c in
                       if uu____3916
                       then
                         let xw =
                           let uu____3921 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3921 in
                         let x =
                           let uu___111_3923 = bv in
                           let uu____3924 =
                             let uu____3927 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3927 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___111_3923.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___111_3923.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3924
                           } in
                         let env3 =
                           let uu___112_3929 = env2 in
                           let uu____3930 =
                             let uu____3932 =
                               let uu____3933 =
                                 let uu____3938 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3938) in
                               FStar_Syntax_Syntax.NT uu____3933 in
                             uu____3932 :: (env2.subst) in
                           {
                             env = (uu___112_3929.env);
                             subst = uu____3930;
                             tc_const = (uu___112_3929.tc_const)
                           } in
                         let uu____3939 =
                           let uu____3941 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3942 =
                             let uu____3944 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3944 :: acc in
                           uu____3941 :: uu____3942 in
                         (env3, uu____3939)
                       else
                         (let x =
                            let uu___113_3948 = bv in
                            let uu____3949 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___113_3948.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___113_3948.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3949
                            } in
                          let uu____3952 =
                            let uu____3954 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3954 :: acc in
                          (env2, uu____3952))) (env1, []) binders1 in
          (match uu____3866 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3966 =
                 let check_what =
                   let uu____3978 = is_monadic what in
                   if uu____3978 then check_m else check_n in
                 let uu____3987 = check_what env2 body1 in
                 match uu____3987 with
                 | (t,s_body,u_body) ->
                     let uu____3997 =
                       let uu____3998 =
                         let uu____3999 = is_monadic what in
                         if uu____3999 then M t else N t in
                       comp_of_nm uu____3998 in
                     (uu____3997, s_body, u_body) in
               (match uu____3966 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____4042 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___95_4045  ->
                                    match uu___95_4045 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____4046 -> false)) in
                          if uu____4042
                          then
                            let double_starred_comp =
                              let uu____4054 =
                                let uu____4055 =
                                  let uu____4056 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____4056 in
                                FStar_All.pipe_left double_star uu____4055 in
                              FStar_Syntax_Syntax.mk_Total uu____4054 in
                            let flags =
                              FStar_List.filter
                                (fun uu___96_4062  ->
                                   match uu___96_4062 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____4063 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____4064 =
                              let uu____4070 =
                                let uu____4071 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____4071 in
                              FStar_Util.Inl uu____4070 in
                            Some uu____4064
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___114_4092 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___114_4092.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___114_4092.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___114_4092.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4096  ->
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
                          let uu____4113 =
                            let uu____4119 =
                              let uu____4123 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___97_4126  ->
                                        match uu___97_4126 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4127 -> false)) in
                              if uu____4123
                              then
                                let uu____4131 =
                                  FStar_List.filter
                                    (fun uu___98_4134  ->
                                       match uu___98_4134 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4135 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4131)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4119 in
                          Some uu____4113 in
                    let uu____4147 =
                      let comp1 =
                        let uu____4159 = is_monadic what in
                        let uu____4160 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4159 uu____4160 in
                      let uu____4161 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4161,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4147 with
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
                FStar_Syntax_Syntax.p = uu____4239;_};
            FStar_Syntax_Syntax.fv_delta = uu____4240;
            FStar_Syntax_Syntax.fv_qual = uu____4241;_}
          ->
          let uu____4243 =
            let uu____4246 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4246 in
          (match uu____4243 with
           | (uu____4262,t) ->
               let uu____4264 = let uu____4265 = normalize1 t in N uu____4265 in
               (uu____4264, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4282 = check_n env head1 in
          (match uu____4282 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4296 =
                   let uu____4297 = FStar_Syntax_Subst.compress t in
                   uu____4297.FStar_Syntax_Syntax.n in
                 match uu____4296 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4300 -> true
                 | uu____4308 -> false in
               let rec flatten1 t =
                 let uu____4320 =
                   let uu____4321 = FStar_Syntax_Subst.compress t in
                   uu____4321.FStar_Syntax_Syntax.n in
                 match uu____4320 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4333);
                                FStar_Syntax_Syntax.tk = uu____4334;
                                FStar_Syntax_Syntax.pos = uu____4335;
                                FStar_Syntax_Syntax.vars = uu____4336;_})
                     when is_arrow t1 ->
                     let uu____4353 = flatten1 t1 in
                     (match uu____4353 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4405,uu____4406)
                     -> flatten1 e1
                 | uu____4435 ->
                     let uu____4436 =
                       let uu____4437 =
                         let uu____4438 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4438 in
                       FStar_Errors.Err uu____4437 in
                     raise uu____4436 in
               let uu____4446 = flatten1 t_head in
               (match uu____4446 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4491 =
                          let uu____4492 =
                            let uu____4493 = FStar_Util.string_of_int n1 in
                            let uu____4497 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4503 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4493 uu____4497 uu____4503 in
                          FStar_Errors.Err uu____4492 in
                        raise uu____4491)
                     else ();
                     (let uu____4508 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4508 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4535 args1 =
                            match uu____4535 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4578 =
                                       let uu____4579 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4579.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4578
                                 | (binders3,[]) ->
                                     let uu____4598 =
                                       let uu____4599 =
                                         let uu____4602 =
                                           let uu____4603 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4603 in
                                         FStar_Syntax_Subst.compress
                                           uu____4602 in
                                       uu____4599.FStar_Syntax_Syntax.n in
                                     (match uu____4598 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4619 =
                                            let uu____4620 =
                                              let uu____4621 =
                                                let uu____4629 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4629) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4621 in
                                            mk1 uu____4620 in
                                          N uu____4619
                                      | uu____4633 -> failwith "wat?")
                                 | ([],uu____4634::uu____4635) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4660)::binders3,(arg,uu____4663)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4697 = FStar_List.splitAt n' binders1 in
                          (match uu____4697 with
                           | (binders2,uu____4714) ->
                               let uu____4727 =
                                 let uu____4737 =
                                   FStar_List.map2
                                     (fun uu____4766  ->
                                        fun uu____4767  ->
                                          match (uu____4766, uu____4767) with
                                          | ((bv,uu____4784),(arg,q)) ->
                                              let uu____4791 =
                                                let uu____4792 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4792.FStar_Syntax_Syntax.n in
                                              (match uu____4791 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4802 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4815 ->
                                                   let uu____4816 =
                                                     check_n env arg in
                                                   (match uu____4816 with
                                                    | (uu____4827,s_arg,u_arg)
                                                        ->
                                                        let uu____4830 =
                                                          let uu____4834 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4834
                                                          then
                                                            let uu____4838 =
                                                              let uu____4841
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4841, q) in
                                                            [uu____4838;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4830))))
                                     binders2 args in
                                 FStar_List.split uu____4737 in
                               (match uu____4727 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4888 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4894 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4888, uu____4894)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4941) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4947) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4953,uu____4954) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4984 = let uu____4985 = env.tc_const c in N uu____4985 in
          (uu____4984, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4986 ->
          let uu____4994 =
            let uu____4995 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4995 in
          failwith uu____4994
      | FStar_Syntax_Syntax.Tm_type uu____4999 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____5003 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____5014 ->
          let uu____5019 =
            let uu____5020 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____5020 in
          failwith uu____5019
      | FStar_Syntax_Syntax.Tm_uvar uu____5024 ->
          let uu____5035 =
            let uu____5036 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____5036 in
          failwith uu____5035
      | FStar_Syntax_Syntax.Tm_delayed uu____5040 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5064 =
            let uu____5065 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____5065 in
          failwith uu____5064
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
          let uu____5102 = check_n env e0 in
          match uu____5102 with
          | (uu____5109,s_e0,u_e0) ->
              let uu____5112 =
                let uu____5129 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5169 = FStar_Syntax_Subst.open_branch b in
                       match uu____5169 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___115_5198 = env in
                             let uu____5199 =
                               let uu____5200 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5200 in
                             {
                               env = uu____5199;
                               subst = (uu___115_5198.subst);
                               tc_const = (uu___115_5198.tc_const)
                             } in
                           let uu____5202 = f env1 body in
                           (match uu____5202 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5248 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5129 in
              (match uu____5112 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5309 = FStar_List.hd nms in
                     match uu____5309 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___99_5315  ->
                          match uu___99_5315 with
                          | M uu____5316 -> true
                          | uu____5317 -> false) nms in
                   let uu____5318 =
                     let uu____5339 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5394  ->
                              match uu____5394 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5502 =
                                         check env original_body (M t2) in
                                       (match uu____5502 with
                                        | (uu____5523,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5548,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5339 in
                   (match uu____5318 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5661  ->
                                 match uu____5661 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5698 =
                                         let uu____5699 =
                                           let uu____5709 =
                                             let uu____5713 =
                                               let uu____5716 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5717 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5716, uu____5717) in
                                             [uu____5713] in
                                           (s_body, uu____5709) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5699 in
                                       mk1 uu____5698 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5738 =
                              let uu____5739 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5739] in
                            let uu____5740 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5742 =
                              let uu____5749 =
                                let uu____5755 =
                                  let uu____5756 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5756 in
                                FStar_Util.Inl uu____5755 in
                              Some uu____5749 in
                            FStar_Syntax_Util.abs uu____5738 uu____5740
                              uu____5742 in
                          let t1_star =
                            let uu____5770 =
                              let uu____5774 =
                                let uu____5775 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5775 in
                              [uu____5774] in
                            let uu____5776 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5770 uu____5776 in
                          let uu____5779 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5809 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5779, uu____5809)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5823 =
                             let uu____5826 =
                               let uu____5827 =
                                 let uu____5845 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5845,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5827 in
                             mk1 uu____5826 in
                           let uu____5872 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5823, uu____5872))))
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
              let uu____5915 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5915] in
            let uu____5916 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5916 with
            | (x_binders1,e21) ->
                let uu____5924 = infer env e1 in
                (match uu____5924 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5935 = is_C t1 in
                       if uu____5935
                       then
                         let uu___116_5936 = binding in
                         let uu____5937 =
                           let uu____5940 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5940 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___116_5936.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___116_5936.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5937;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___116_5936.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___116_5936.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___117_5943 = env in
                       let uu____5944 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___118_5946 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___118_5946.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___118_5946.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5944;
                         subst = (uu___117_5943.subst);
                         tc_const = (uu___117_5943.tc_const)
                       } in
                     let uu____5947 = proceed env1 e21 in
                     (match uu____5947 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___119_5958 = binding in
                            let uu____5959 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___119_5958.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___119_5958.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5959;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___119_5958.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___119_5958.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5962 =
                            let uu____5965 =
                              let uu____5966 =
                                let uu____5974 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___120_5980 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___120_5980.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___120_5980.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___120_5980.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___120_5980.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5974) in
                              FStar_Syntax_Syntax.Tm_let uu____5966 in
                            mk1 uu____5965 in
                          let uu____5981 =
                            let uu____5984 =
                              let uu____5985 =
                                let uu____5993 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___121_5999 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5999.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5999.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5999.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5999.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5993) in
                              FStar_Syntax_Syntax.Tm_let uu____5985 in
                            mk1 uu____5984 in
                          (nm_rec, uu____5962, uu____5981))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___122_6008 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___122_6008.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___122_6008.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___122_6008.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___123_6010 = env in
                       let uu____6011 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___124_6013 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_6013.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_6013.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____6011;
                         subst = (uu___123_6010.subst);
                         tc_const = (uu___123_6010.tc_const)
                       } in
                     let uu____6014 = ensure_m env1 e21 in
                     (match uu____6014 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____6031 =
                              let uu____6032 =
                                let uu____6042 =
                                  let uu____6046 =
                                    let uu____6049 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6050 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6049, uu____6050) in
                                  [uu____6046] in
                                (s_e2, uu____6042) in
                              FStar_Syntax_Syntax.Tm_app uu____6032 in
                            mk1 uu____6031 in
                          let s_e22 =
                            let uu____6059 =
                              let uu____6066 =
                                let uu____6072 =
                                  let uu____6073 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6073 in
                                FStar_Util.Inl uu____6072 in
                              Some uu____6066 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6059 in
                          let body =
                            let uu____6087 =
                              let uu____6088 =
                                let uu____6098 =
                                  let uu____6102 =
                                    let uu____6105 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6105) in
                                  [uu____6102] in
                                (s_e1, uu____6098) in
                              FStar_Syntax_Syntax.Tm_app uu____6088 in
                            mk1 uu____6087 in
                          let uu____6113 =
                            let uu____6114 =
                              let uu____6115 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6115] in
                            let uu____6116 =
                              let uu____6123 =
                                let uu____6129 =
                                  let uu____6130 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6130 in
                                FStar_Util.Inl uu____6129 in
                              Some uu____6123 in
                            FStar_Syntax_Util.abs uu____6114 body uu____6116 in
                          let uu____6141 =
                            let uu____6144 =
                              let uu____6145 =
                                let uu____6153 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___125_6159 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_6159.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_6159.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_6159.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_6159.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6153) in
                              FStar_Syntax_Syntax.Tm_let uu____6145 in
                            mk1 uu____6144 in
                          ((M t2), uu____6113, uu____6141)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6168 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6168 in
      let uu____6173 = check env e mn in
      match uu____6173 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6183 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6196 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6196 in
      let uu____6201 = check env e mn in
      match uu____6201 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6211 -> failwith "[check_m]: impossible"
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
        (let uu____6233 =
           let uu____6234 = is_C c in Prims.op_Negation uu____6234 in
         if uu____6233 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6246 =
           let uu____6247 = FStar_Syntax_Subst.compress c in
           uu____6247.FStar_Syntax_Syntax.n in
         match uu____6246 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6266 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6266 with
              | (wp_head,wp_args) ->
                  ((let uu____6293 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6307 =
                           let uu____6308 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6308 in
                         Prims.op_Negation uu____6307) in
                    if uu____6293 then failwith "mismatch" else ());
                   (let uu____6317 =
                      let uu____6318 =
                        let uu____6328 =
                          FStar_List.map2
                            (fun uu____6347  ->
                               fun uu____6348  ->
                                 match (uu____6347, uu____6348) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6371 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6371
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6374 = print_implicit q in
                                         let uu____6375 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6374 uu____6375)
                                      else ();
                                      (let uu____6377 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6377, q)))) args wp_args in
                        (head1, uu____6328) in
                      FStar_Syntax_Syntax.Tm_app uu____6318 in
                    mk1 uu____6317)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6399 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6399 with
              | (binders_orig,comp1) ->
                  let uu____6404 =
                    let uu____6412 =
                      FStar_List.map
                        (fun uu____6433  ->
                           match uu____6433 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6446 = is_C h in
                               if uu____6446
                               then
                                 let w' =
                                   let uu____6453 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6453 in
                                 let uu____6454 =
                                   let uu____6458 =
                                     let uu____6462 =
                                       let uu____6465 =
                                         let uu____6466 =
                                           let uu____6467 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6467 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6466 in
                                       (uu____6465, q) in
                                     [uu____6462] in
                                   (w', q) :: uu____6458 in
                                 (w', uu____6454)
                               else
                                 (let x =
                                    let uu____6479 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6479 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6412 in
                  (match uu____6404 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6509 =
                           let uu____6511 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6511 in
                         FStar_Syntax_Subst.subst_comp uu____6509 comp1 in
                       let app =
                         let uu____6515 =
                           let uu____6516 =
                             let uu____6526 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6536 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6537 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6536, uu____6537)) bvs in
                             (wp, uu____6526) in
                           FStar_Syntax_Syntax.Tm_app uu____6516 in
                         mk1 uu____6515 in
                       let comp3 =
                         let uu____6542 = type_of_comp comp2 in
                         let uu____6543 = is_monadic_comp comp2 in
                         trans_G env uu____6542 uu____6543 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6545,uu____6546) ->
             trans_F_ env e wp
         | uu____6575 -> failwith "impossible trans_F_")
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
            let uu____6580 =
              let uu____6581 = star_type' env h in
              let uu____6584 =
                let uu____6590 =
                  let uu____6593 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6593) in
                [uu____6590] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6581;
                FStar_Syntax_Syntax.effect_args = uu____6584;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6580
          else
            (let uu____6599 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6599)
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
    fun t  -> let uu____6610 = n env.env t in star_type' env uu____6610
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6622 = n env.env t in check_n env uu____6622
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6632 = n env.env c in
        let uu____6633 = n env.env wp in trans_F_ env uu____6632 uu____6633