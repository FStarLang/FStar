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
              let uu___100_64 = a in
              let uu____65 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___100_64.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___100_64.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____73 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____73
             then
               (d "Elaborating extra WP combinators";
                (let uu____75 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____75))
             else ());
            (let rec collect_binders t =
               let uu____84 =
                 let uu____85 =
                   let uu____88 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____88 in
                 uu____85.FStar_Syntax_Syntax.n in
               match uu____84 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____110) -> t1
                     | uu____117 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____120 = collect_binders rest in
                   FStar_List.append bs uu____120
               | FStar_Syntax_Syntax.Tm_type uu____126 -> []
               | uu____129 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____141 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____141 FStar_Syntax_Util.name_binders in
             (let uu____152 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____152
              then
                let uu____153 =
                  let uu____154 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____154 in
                d uu____153
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange in
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
                  (fun uu____215  ->
                     match uu____215 with
                     | (t,b) ->
                         let uu____222 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____222)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____239 = FStar_Syntax_Syntax.as_implicit true in
                     ((fst t), uu____239)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____252 = FStar_Syntax_Syntax.bv_to_name (fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____252) in
              let uu____253 =
                let uu____265 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let body =
                      let uu____285 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____285 in
                    let uu____288 =
                      let uu____289 =
                        let uu____293 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____294 =
                          let uu____296 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____296] in
                        uu____293 :: uu____294 in
                      FStar_List.append binders uu____289 in
                    FStar_Syntax_Util.abs uu____288 body None in
                  let uu____304 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____305 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____304, uu____305) in
                match uu____265 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____336 =
                        let uu____337 =
                          let uu____347 =
                            let uu____351 =
                              FStar_List.map
                                (fun uu____359  ->
                                   match uu____359 with
                                   | (bv,uu____365) ->
                                       let uu____366 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____367 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____366, uu____367)) binders in
                            let uu____368 =
                              let uu____372 =
                                let uu____375 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____376 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____375, uu____376) in
                              let uu____377 =
                                let uu____381 =
                                  let uu____384 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____384) in
                                [uu____381] in
                              uu____372 :: uu____377 in
                            FStar_List.append uu____351 uu____368 in
                          (fv, uu____347) in
                        FStar_Syntax_Syntax.Tm_app uu____337 in
                      mk1 uu____336 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____253 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____430 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____430 in
                    let ret1 =
                      let uu____438 =
                        let uu____444 =
                          let uu____445 =
                            let uu____448 =
                              let uu____449 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____449 in
                            FStar_Syntax_Syntax.mk_Total uu____448 in
                          FStar_Syntax_Util.lcomp_of_comp uu____445 in
                        FStar_Util.Inl uu____444 in
                      Some uu____438 in
                    let body =
                      let uu____459 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____459 ret1 in
                    let uu____460 =
                      let uu____461 = mk_all_implicit binders in
                      let uu____465 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____461 uu____465 in
                    FStar_Syntax_Util.abs uu____460 body ret1 in
                  let c_pure1 =
                    let uu____480 = mk_lid "pure" in
                    register env1 uu____480 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____485 =
                        let uu____486 =
                          let uu____487 =
                            let uu____491 =
                              let uu____492 =
                                let uu____493 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____493 in
                              FStar_Syntax_Syntax.mk_binder uu____492 in
                            [uu____491] in
                          let uu____494 =
                            let uu____497 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____497 in
                          FStar_Syntax_Util.arrow uu____487 uu____494 in
                        mk_gctx uu____486 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____485 in
                    let r =
                      let uu____499 =
                        let uu____500 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____500 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____499 in
                    let ret1 =
                      let uu____508 =
                        let uu____514 =
                          let uu____515 =
                            let uu____518 =
                              let uu____519 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____519 in
                            FStar_Syntax_Syntax.mk_Total uu____518 in
                          FStar_Syntax_Util.lcomp_of_comp uu____515 in
                        FStar_Util.Inl uu____514 in
                      Some uu____508 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____534 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____537 =
                          let uu____543 =
                            let uu____545 =
                              let uu____546 =
                                let uu____547 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____547
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____546 in
                            [uu____545] in
                          FStar_List.append gamma_as_args uu____543 in
                        FStar_Syntax_Util.mk_app uu____534 uu____537 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____550 =
                      let uu____551 = mk_all_implicit binders in
                      let uu____555 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____551 uu____555 in
                    FStar_Syntax_Util.abs uu____550 outer_body ret1 in
                  let c_app1 =
                    let uu____574 = mk_lid "app" in
                    register env1 uu____574 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____581 =
                        let uu____585 =
                          let uu____586 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____586 in
                        [uu____585] in
                      let uu____587 =
                        let uu____590 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____590 in
                      FStar_Syntax_Util.arrow uu____581 uu____587 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____593 =
                        let uu____594 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____594 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____593 in
                    let ret1 =
                      let uu____602 =
                        let uu____608 =
                          let uu____609 =
                            let uu____612 =
                              let uu____613 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____613 in
                            FStar_Syntax_Syntax.mk_Total uu____612 in
                          FStar_Syntax_Util.lcomp_of_comp uu____609 in
                        FStar_Util.Inl uu____608 in
                      Some uu____602 in
                    let uu____622 =
                      let uu____623 = mk_all_implicit binders in
                      let uu____627 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____623 uu____627 in
                    let uu____645 =
                      let uu____646 =
                        let uu____652 =
                          let uu____654 =
                            let uu____657 =
                              let uu____663 =
                                let uu____665 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____665] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____663 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____657 in
                          let uu____666 =
                            let uu____670 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____670] in
                          uu____654 :: uu____666 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____652 in
                      FStar_Syntax_Util.mk_app c_app1 uu____646 in
                    FStar_Syntax_Util.abs uu____622 uu____645 ret1 in
                  let c_lift11 =
                    let uu____674 = mk_lid "lift1" in
                    register env1 uu____674 c_lift1 in
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
                      let uu____682 =
                        let uu____686 =
                          let uu____687 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____687 in
                        let uu____688 =
                          let uu____690 =
                            let uu____691 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____691 in
                          [uu____690] in
                        uu____686 :: uu____688 in
                      let uu____692 =
                        let uu____695 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____695 in
                      FStar_Syntax_Util.arrow uu____682 uu____692 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____698 =
                        let uu____699 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____699 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____698 in
                    let a2 =
                      let uu____701 =
                        let uu____702 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____702 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____701 in
                    let ret1 =
                      let uu____710 =
                        let uu____716 =
                          let uu____717 =
                            let uu____720 =
                              let uu____721 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____721 in
                            FStar_Syntax_Syntax.mk_Total uu____720 in
                          FStar_Syntax_Util.lcomp_of_comp uu____717 in
                        FStar_Util.Inl uu____716 in
                      Some uu____710 in
                    let uu____730 =
                      let uu____731 = mk_all_implicit binders in
                      let uu____735 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____731 uu____735 in
                    let uu____757 =
                      let uu____758 =
                        let uu____764 =
                          let uu____766 =
                            let uu____769 =
                              let uu____775 =
                                let uu____777 =
                                  let uu____780 =
                                    let uu____786 =
                                      let uu____788 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____788] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____786 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____780 in
                                let uu____789 =
                                  let uu____793 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____793] in
                                uu____777 :: uu____789 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____775 in
                            FStar_Syntax_Util.mk_app c_app1 uu____769 in
                          let uu____796 =
                            let uu____800 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____800] in
                          uu____766 :: uu____796 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____764 in
                      FStar_Syntax_Util.mk_app c_app1 uu____758 in
                    FStar_Syntax_Util.abs uu____730 uu____757 ret1 in
                  let c_lift21 =
                    let uu____804 = mk_lid "lift2" in
                    register env1 uu____804 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____811 =
                        let uu____815 =
                          let uu____816 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____816 in
                        [uu____815] in
                      let uu____817 =
                        let uu____820 =
                          let uu____821 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____821 in
                        FStar_Syntax_Syntax.mk_Total uu____820 in
                      FStar_Syntax_Util.arrow uu____811 uu____817 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____830 =
                        let uu____836 =
                          let uu____837 =
                            let uu____840 =
                              let uu____841 =
                                let uu____842 =
                                  let uu____846 =
                                    let uu____847 =
                                      FStar_Syntax_Syntax.bv_to_name t1 in
                                    FStar_Syntax_Syntax.null_binder uu____847 in
                                  [uu____846] in
                                let uu____848 =
                                  let uu____851 =
                                    FStar_Syntax_Syntax.bv_to_name t2 in
                                  FStar_Syntax_Syntax.mk_GTotal uu____851 in
                                FStar_Syntax_Util.arrow uu____842 uu____848 in
                              mk_ctx uu____841 in
                            FStar_Syntax_Syntax.mk_Total uu____840 in
                          FStar_Syntax_Util.lcomp_of_comp uu____837 in
                        FStar_Util.Inl uu____836 in
                      Some uu____830 in
                    let e1 =
                      let uu____861 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____861 in
                    let body =
                      let uu____863 =
                        let uu____864 =
                          let uu____868 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____868] in
                        FStar_List.append gamma uu____864 in
                      let uu____871 =
                        let uu____872 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____875 =
                          let uu____881 =
                            let uu____882 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____882 in
                          let uu____883 = args_of_binders1 gamma in uu____881
                            :: uu____883 in
                        FStar_Syntax_Util.mk_app uu____872 uu____875 in
                      FStar_Syntax_Util.abs uu____863 uu____871 ret1 in
                    let uu____885 =
                      let uu____886 = mk_all_implicit binders in
                      let uu____890 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____886 uu____890 in
                    FStar_Syntax_Util.abs uu____885 body ret1 in
                  let c_push1 =
                    let uu____907 = mk_lid "push" in
                    register env1 uu____907 c_push in
                  let ret_tot_wp_a =
                    let uu____915 =
                      let uu____921 =
                        let uu____922 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____922 in
                      FStar_Util.Inl uu____921 in
                    Some uu____915 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____950 =
                        let uu____951 =
                          let uu____961 = args_of_binders1 binders in
                          (c, uu____961) in
                        FStar_Syntax_Syntax.Tm_app uu____951 in
                      mk1 uu____950
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____969 =
                        let uu____970 =
                          let uu____974 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____975 =
                            let uu____977 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____977] in
                          uu____974 :: uu____975 in
                        let uu____978 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____970 uu____978 in
                      FStar_Syntax_Syntax.mk_Total uu____969 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____982 =
                      let uu____983 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____983 in
                    let uu____989 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____991 =
                        let uu____994 =
                          let uu____1000 =
                            let uu____1002 =
                              let uu____1005 =
                                let uu____1011 =
                                  let uu____1012 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1012 in
                                [uu____1011] in
                              FStar_Syntax_Util.mk_app l_ite uu____1005 in
                            [uu____1002] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1000 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____994 in
                      FStar_Syntax_Util.ascribe uu____991
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____982 uu____989
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1037 = mk_lid "wp_if_then_else" in
                    register env1 uu____1037 wp_if_then_else in
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
                      let uu____1048 =
                        let uu____1054 =
                          let uu____1056 =
                            let uu____1059 =
                              let uu____1065 =
                                let uu____1067 =
                                  let uu____1070 =
                                    let uu____1076 =
                                      let uu____1077 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1077 in
                                    [uu____1076] in
                                  FStar_Syntax_Util.mk_app l_and uu____1070 in
                                [uu____1067] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1065 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1059 in
                          let uu____1082 =
                            let uu____1086 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1086] in
                          uu____1056 :: uu____1082 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1054 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1048 in
                    let uu____1089 =
                      let uu____1090 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1090 in
                    FStar_Syntax_Util.abs uu____1089 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1097 = mk_lid "wp_assert" in
                    register env1 uu____1097 wp_assert in
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
                      let uu____1108 =
                        let uu____1114 =
                          let uu____1116 =
                            let uu____1119 =
                              let uu____1125 =
                                let uu____1127 =
                                  let uu____1130 =
                                    let uu____1136 =
                                      let uu____1137 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1137 in
                                    [uu____1136] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1130 in
                                [uu____1127] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1125 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1119 in
                          let uu____1142 =
                            let uu____1146 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1146] in
                          uu____1116 :: uu____1142 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1114 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1108 in
                    let uu____1149 =
                      let uu____1150 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1150 in
                    FStar_Syntax_Util.abs uu____1149 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1157 = mk_lid "wp_assume" in
                    register env1 uu____1157 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1166 =
                        let uu____1170 =
                          let uu____1171 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1171 in
                        [uu____1170] in
                      let uu____1172 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1166 uu____1172 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1179 =
                        let uu____1185 =
                          let uu____1187 =
                            let uu____1190 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1190 in
                          let uu____1196 =
                            let uu____1200 =
                              let uu____1203 =
                                let uu____1209 =
                                  let uu____1211 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1211] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1209 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1203 in
                            [uu____1200] in
                          uu____1187 :: uu____1196 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1185 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1179 in
                    let uu____1218 =
                      let uu____1219 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1219 in
                    FStar_Syntax_Util.abs uu____1218 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1226 = mk_lid "wp_close" in
                    register env1 uu____1226 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1237 =
                      let uu____1243 =
                        let uu____1244 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1244 in
                      FStar_Util.Inl uu____1243 in
                    Some uu____1237 in
                  let ret_gtot_type =
                    let uu____1264 =
                      let uu____1270 =
                        let uu____1271 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1271 in
                      FStar_Util.Inl uu____1270 in
                    Some uu____1264 in
                  let mk_forall1 x body =
                    let uu____1291 =
                      let uu____1294 =
                        let uu____1295 =
                          let uu____1305 =
                            let uu____1307 =
                              let uu____1308 =
                                let uu____1309 =
                                  let uu____1310 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1310] in
                                FStar_Syntax_Util.abs uu____1309 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1308 in
                            [uu____1307] in
                          (FStar_Syntax_Util.tforall, uu____1305) in
                        FStar_Syntax_Syntax.Tm_app uu____1295 in
                      FStar_Syntax_Syntax.mk uu____1294 in
                    uu____1291 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1324 =
                      let uu____1325 = FStar_Syntax_Subst.compress t in
                      uu____1325.FStar_Syntax_Syntax.n in
                    match uu____1324 with
                    | FStar_Syntax_Syntax.Tm_type uu____1328 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1343  ->
                              match uu____1343 with
                              | (b,uu____1347) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1348 -> true in
                  let rec is_monotonic t =
                    let uu____1353 =
                      let uu____1354 = FStar_Syntax_Subst.compress t in
                      uu____1354.FStar_Syntax_Syntax.n in
                    match uu____1353 with
                    | FStar_Syntax_Syntax.Tm_type uu____1357 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1372  ->
                              match uu____1372 with
                              | (b,uu____1376) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1377 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1429 =
                      let uu____1430 = FStar_Syntax_Subst.compress t1 in
                      uu____1430.FStar_Syntax_Syntax.n in
                    match uu____1429 with
                    | FStar_Syntax_Syntax.Tm_type uu____1433 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1436);
                                      FStar_Syntax_Syntax.tk = uu____1437;
                                      FStar_Syntax_Syntax.pos = uu____1438;
                                      FStar_Syntax_Syntax.vars = uu____1439;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1462 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1462
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1465 =
                              let uu____1468 =
                                let uu____1474 =
                                  let uu____1475 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1475 in
                                [uu____1474] in
                              FStar_Syntax_Util.mk_app x uu____1468 in
                            let uu____1476 =
                              let uu____1479 =
                                let uu____1485 =
                                  let uu____1486 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1486 in
                                [uu____1485] in
                              FStar_Syntax_Util.mk_app y uu____1479 in
                            mk_rel1 b uu____1465 uu____1476 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1493 =
                               let uu____1494 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1497 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1494 uu____1497 in
                             let uu____1500 =
                               let uu____1501 =
                                 let uu____1504 =
                                   let uu____1510 =
                                     let uu____1511 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1511 in
                                   [uu____1510] in
                                 FStar_Syntax_Util.mk_app x uu____1504 in
                               let uu____1512 =
                                 let uu____1515 =
                                   let uu____1521 =
                                     let uu____1522 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1522 in
                                   [uu____1521] in
                                 FStar_Syntax_Util.mk_app y uu____1515 in
                               mk_rel1 b uu____1501 uu____1512 in
                             FStar_Syntax_Util.mk_imp uu____1493 uu____1500 in
                           let uu____1523 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1523)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1526);
                                      FStar_Syntax_Syntax.tk = uu____1527;
                                      FStar_Syntax_Syntax.pos = uu____1528;
                                      FStar_Syntax_Syntax.vars = uu____1529;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1552 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1552
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1555 =
                              let uu____1558 =
                                let uu____1564 =
                                  let uu____1565 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1565 in
                                [uu____1564] in
                              FStar_Syntax_Util.mk_app x uu____1558 in
                            let uu____1566 =
                              let uu____1569 =
                                let uu____1575 =
                                  let uu____1576 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1576 in
                                [uu____1575] in
                              FStar_Syntax_Util.mk_app y uu____1569 in
                            mk_rel1 b uu____1555 uu____1566 in
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
                      let uu____1682 =
                        let uu____1683 = FStar_Syntax_Subst.compress t1 in
                        uu____1683.FStar_Syntax_Syntax.n in
                      match uu____1682 with
                      | FStar_Syntax_Syntax.Tm_type uu____1688 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1705 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1705
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1720 =
                                let uu____1721 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1721 i in
                              FStar_Syntax_Syntax.fvar uu____1720
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1742 =
                            let uu____1750 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1759  ->
                                     match uu____1759 with
                                     | (t2,q) ->
                                         let uu____1766 = project i x in
                                         let uu____1767 = project i y in
                                         mk_stronger t2 uu____1766 uu____1767)
                                args in
                            match uu____1750 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1742 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1814);
                                      FStar_Syntax_Syntax.tk = uu____1815;
                                      FStar_Syntax_Syntax.pos = uu____1816;
                                      FStar_Syntax_Syntax.vars = uu____1817;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1839  ->
                                   match uu____1839 with
                                   | (bv,q) ->
                                       let uu____1844 =
                                         let uu____1845 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1845 in
                                       FStar_Syntax_Syntax.gen_bv uu____1844
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1849 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1849) bvs in
                          let body =
                            let uu____1853 = FStar_Syntax_Util.mk_app x args in
                            let uu____1854 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1853 uu____1854 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1859);
                                      FStar_Syntax_Syntax.tk = uu____1860;
                                      FStar_Syntax_Syntax.pos = uu____1861;
                                      FStar_Syntax_Syntax.vars = uu____1862;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1884  ->
                                   match uu____1884 with
                                   | (bv,q) ->
                                       let uu____1889 =
                                         let uu____1890 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1890 in
                                       FStar_Syntax_Syntax.gen_bv uu____1889
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1894 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1894) bvs in
                          let body =
                            let uu____1898 = FStar_Syntax_Util.mk_app x args in
                            let uu____1899 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1898 uu____1899 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1902 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1908 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1909 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1910 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1908 uu____1909 uu____1910 in
                    let uu____1911 =
                      let uu____1912 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1912 in
                    FStar_Syntax_Util.abs uu____1911 body ret_tot_type in
                  let stronger1 =
                    let uu____1927 = mk_lid "stronger" in
                    register env1 uu____1927 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1933 = FStar_Util.prefix gamma in
                    match uu____1933 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1959 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1959 in
                          let uu____1962 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1962 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1970 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1970 in
                              let guard_free1 =
                                let uu____1977 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1977 in
                              let pat =
                                let uu____1981 =
                                  let uu____1987 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1987] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1981 in
                              let pattern_guarded_body =
                                let uu____1991 =
                                  let uu____1992 =
                                    let uu____1997 =
                                      let uu____1998 =
                                        let uu____2005 =
                                          let uu____2007 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2007] in
                                        [uu____2005] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1998 in
                                    (body, uu____1997) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1992 in
                                mk1 uu____1991 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2010 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2013 =
                            let uu____2014 =
                              let uu____2015 =
                                let uu____2016 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2019 =
                                  let uu____2025 = args_of_binders1 wp_args in
                                  let uu____2027 =
                                    let uu____2029 =
                                      let uu____2030 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2030 in
                                    [uu____2029] in
                                  FStar_List.append uu____2025 uu____2027 in
                                FStar_Syntax_Util.mk_app uu____2016
                                  uu____2019 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2015 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2014 in
                          FStar_Syntax_Util.abs gamma uu____2013
                            ret_gtot_type in
                        let uu____2031 =
                          let uu____2032 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2032 in
                        FStar_Syntax_Util.abs uu____2031 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2039 = mk_lid "wp_ite" in
                    register env1 uu____2039 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2045 = FStar_Util.prefix gamma in
                    match uu____2045 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2069 =
                            let uu____2070 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2073 =
                              let uu____2079 =
                                let uu____2080 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2080 in
                              [uu____2079] in
                            FStar_Syntax_Util.mk_app uu____2070 uu____2073 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2069 in
                        let uu____2081 =
                          let uu____2082 =
                            let uu____2086 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2086 gamma in
                          FStar_List.append binders uu____2082 in
                        FStar_Syntax_Util.abs uu____2081 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2095 = mk_lid "null_wp" in
                    register env1 uu____2095 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2104 =
                        let uu____2110 =
                          let uu____2112 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2113 =
                            let uu____2115 =
                              let uu____2118 =
                                let uu____2124 =
                                  let uu____2125 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2125 in
                                [uu____2124] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2118 in
                            let uu____2126 =
                              let uu____2130 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2130] in
                            uu____2115 :: uu____2126 in
                          uu____2112 :: uu____2113 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2110 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2104 in
                    let uu____2133 =
                      let uu____2134 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2134 in
                    FStar_Syntax_Util.abs uu____2133 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2141 = mk_lid "wp_trivial" in
                    register env1 uu____2141 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2146 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2146
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2151 =
                      let uu____2153 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2153 in
                    let uu____2158 =
                      let uu___102_2159 = ed in
                      let uu____2160 =
                        let uu____2161 = c wp_if_then_else2 in
                        ([], uu____2161) in
                      let uu____2163 =
                        let uu____2164 = c wp_ite2 in ([], uu____2164) in
                      let uu____2166 =
                        let uu____2167 = c stronger2 in ([], uu____2167) in
                      let uu____2169 =
                        let uu____2170 = c wp_close2 in ([], uu____2170) in
                      let uu____2172 =
                        let uu____2173 = c wp_assert2 in ([], uu____2173) in
                      let uu____2175 =
                        let uu____2176 = c wp_assume2 in ([], uu____2176) in
                      let uu____2178 =
                        let uu____2179 = c null_wp2 in ([], uu____2179) in
                      let uu____2181 =
                        let uu____2182 = c wp_trivial2 in ([], uu____2182) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___102_2159.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___102_2159.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___102_2159.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___102_2159.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___102_2159.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___102_2159.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___102_2159.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2160;
                        FStar_Syntax_Syntax.ite_wp = uu____2163;
                        FStar_Syntax_Syntax.stronger = uu____2166;
                        FStar_Syntax_Syntax.close_wp = uu____2169;
                        FStar_Syntax_Syntax.assert_p = uu____2172;
                        FStar_Syntax_Syntax.assume_p = uu____2175;
                        FStar_Syntax_Syntax.null_wp = uu____2178;
                        FStar_Syntax_Syntax.trivial = uu____2181;
                        FStar_Syntax_Syntax.repr =
                          (uu___102_2159.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___102_2159.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___102_2159.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___102_2159.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2151, uu____2158)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___103_2194 = dmff_env in
      {
        env = env';
        subst = (uu___103_2194.subst);
        tc_const = (uu___103_2194.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2205 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2217 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___89_2227  ->
    match uu___89_2227 with
    | FStar_Syntax_Syntax.Total (t,uu____2229) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___88_2238  ->
                match uu___88_2238 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2239 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2241 =
          let uu____2242 =
            let uu____2243 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2243 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2242 in
        failwith uu____2241
    | FStar_Syntax_Syntax.GTotal uu____2244 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___90_2252  ->
    match uu___90_2252 with
    | N t ->
        let uu____2254 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2254
    | M t ->
        let uu____2256 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2256
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2260,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2262;
                      FStar_Syntax_Syntax.pos = uu____2263;
                      FStar_Syntax_Syntax.vars = uu____2264;_})
        -> nm_of_comp n2
    | uu____2275 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2287 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2287 with | M uu____2288 -> true | N uu____2289 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2293 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2303 =
        let uu____2307 =
          let uu____2308 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2308 in
        [uu____2307] in
      let uu____2309 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2303 uu____2309 in
    let uu____2312 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2312
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
          (let uu____2347 =
             let uu____2355 =
               let uu____2359 =
                 let uu____2362 =
                   let uu____2363 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2363 in
                 let uu____2364 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2362, uu____2364) in
               [uu____2359] in
             let uu____2369 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2355, uu____2369) in
           FStar_Syntax_Syntax.Tm_arrow uu____2347)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2398) ->
          let binders1 =
            FStar_List.map
              (fun uu____2417  ->
                 match uu____2417 with
                 | (bv,aqual) ->
                     let uu____2424 =
                       let uu___104_2425 = bv in
                       let uu____2426 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___104_2425.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___104_2425.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2426
                       } in
                     (uu____2424, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2429,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2431);
                             FStar_Syntax_Syntax.tk = uu____2432;
                             FStar_Syntax_Syntax.pos = uu____2433;
                             FStar_Syntax_Syntax.vars = uu____2434;_})
               ->
               let uu____2451 =
                 let uu____2452 =
                   let uu____2460 =
                     let uu____2461 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2461 in
                   (binders1, uu____2460) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2452 in
               mk1 uu____2451
           | uu____2465 ->
               let uu____2466 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2466 with
                | N hn ->
                    let uu____2468 =
                      let uu____2469 =
                        let uu____2477 =
                          let uu____2478 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2478 in
                        (binders1, uu____2477) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2469 in
                    mk1 uu____2468
                | M a ->
                    let uu____2483 =
                      let uu____2484 =
                        let uu____2492 =
                          let uu____2496 =
                            let uu____2500 =
                              let uu____2503 =
                                let uu____2504 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2504 in
                              let uu____2505 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2503, uu____2505) in
                            [uu____2500] in
                          FStar_List.append binders1 uu____2496 in
                        let uu____2512 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2492, uu____2512) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2484 in
                    mk1 uu____2483))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2563 = f x in
                    FStar_Util.string_builder_append strb uu____2563);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2567 = f x1 in
                         FStar_Util.string_builder_append strb uu____2567))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2569 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2570 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2569 uu____2570 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2578 =
              let uu____2579 = FStar_Syntax_Subst.compress ty in
              uu____2579.FStar_Syntax_Syntax.n in
            match uu____2578 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2594 =
                  let uu____2595 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2595 in
                if uu____2594
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2609 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2609 s in
                       let uu____2611 =
                         let uu____2612 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2612 in
                       if uu____2611
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2615 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2615 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2626  ->
                                  match uu____2626 with
                                  | (bv,uu____2632) ->
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
            | uu____2645 ->
                ((let uu____2647 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2647);
                 false) in
          let rec is_valid_application head2 =
            let uu____2652 =
              let uu____2653 = FStar_Syntax_Subst.compress head2 in
              uu____2653.FStar_Syntax_Syntax.n in
            match uu____2652 with
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
                  (let uu____2657 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2657)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2670 -> true
                 | uu____2680 ->
                     ((let uu____2682 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2682);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2683 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2684 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2686) ->
                is_valid_application t2
            | uu____2691 -> false in
          let uu____2692 = is_valid_application head1 in
          if uu____2692
          then
            let uu____2693 =
              let uu____2694 =
                let uu____2704 =
                  FStar_List.map
                    (fun uu____2714  ->
                       match uu____2714 with
                       | (t2,qual) ->
                           let uu____2727 = star_type' env t2 in
                           (uu____2727, qual)) args in
                (head1, uu____2704) in
              FStar_Syntax_Syntax.Tm_app uu____2694 in
            mk1 uu____2693
          else
            (let uu____2734 =
               let uu____2735 =
                 let uu____2736 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2736 in
               FStar_Errors.Err uu____2735 in
             raise uu____2734)
      | FStar_Syntax_Syntax.Tm_bvar uu____2737 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2738 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2739 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2740 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2766 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2766 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___107_2772 = env in
                 let uu____2773 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2773;
                   subst = (uu___107_2772.subst);
                   tc_const = (uu___107_2772.tc_const)
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
               ((let uu___108_2790 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___108_2790.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___108_2790.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2797 =
            let uu____2798 =
              let uu____2803 = star_type' env t2 in (uu____2803, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2798 in
          mk1 uu____2797
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2841 =
            let uu____2842 =
              let uu____2860 = star_type' env e in
              let uu____2861 =
                let uu____2871 =
                  let uu____2876 = star_type' env t2 in
                  FStar_Util.Inl uu____2876 in
                (uu____2871, None) in
              (uu____2860, uu____2861, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2842 in
          mk1 uu____2841
      | FStar_Syntax_Syntax.Tm_ascribed uu____2898 ->
          let uu____2916 =
            let uu____2917 =
              let uu____2918 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2918 in
            FStar_Errors.Err uu____2917 in
          raise uu____2916
      | FStar_Syntax_Syntax.Tm_refine uu____2919 ->
          let uu____2924 =
            let uu____2925 =
              let uu____2926 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2926 in
            FStar_Errors.Err uu____2925 in
          raise uu____2924
      | FStar_Syntax_Syntax.Tm_uinst uu____2927 ->
          let uu____2932 =
            let uu____2933 =
              let uu____2934 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2934 in
            FStar_Errors.Err uu____2933 in
          raise uu____2932
      | FStar_Syntax_Syntax.Tm_constant uu____2935 ->
          let uu____2936 =
            let uu____2937 =
              let uu____2938 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2938 in
            FStar_Errors.Err uu____2937 in
          raise uu____2936
      | FStar_Syntax_Syntax.Tm_match uu____2939 ->
          let uu____2955 =
            let uu____2956 =
              let uu____2957 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2957 in
            FStar_Errors.Err uu____2956 in
          raise uu____2955
      | FStar_Syntax_Syntax.Tm_let uu____2958 ->
          let uu____2966 =
            let uu____2967 =
              let uu____2968 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2968 in
            FStar_Errors.Err uu____2967 in
          raise uu____2966
      | FStar_Syntax_Syntax.Tm_uvar uu____2969 ->
          let uu____2978 =
            let uu____2979 =
              let uu____2980 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2980 in
            FStar_Errors.Err uu____2979 in
          raise uu____2978
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2981 =
            let uu____2982 =
              let uu____2983 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2983 in
            FStar_Errors.Err uu____2982 in
          raise uu____2981
      | FStar_Syntax_Syntax.Tm_delayed uu____2984 -> failwith "impossible"
let is_monadic uu___92_3017 =
  match uu___92_3017 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3029;
        FStar_Syntax_Syntax.res_typ = uu____3030;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3032;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_3049  ->
              match uu___91_3049 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3050 -> false))
  | Some (FStar_Util.Inr (uu____3051,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_3064  ->
              match uu___91_3064 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3065 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3069 =
      let uu____3070 = FStar_Syntax_Subst.compress t in
      uu____3070.FStar_Syntax_Syntax.n in
    match uu____3069 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3090 =
            let uu____3091 = FStar_List.hd args in fst uu____3091 in
          is_C uu____3090 in
        if r
        then
          ((let uu____3103 =
              let uu____3104 =
                FStar_List.for_all
                  (fun uu____3107  ->
                     match uu____3107 with | (h,uu____3111) -> is_C h) args in
              Prims.op_Negation uu____3104 in
            if uu____3103 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3115 =
              let uu____3116 =
                FStar_List.for_all
                  (fun uu____3119  ->
                     match uu____3119 with
                     | (h,uu____3123) ->
                         let uu____3124 = is_C h in
                         Prims.op_Negation uu____3124) args in
              Prims.op_Negation uu____3116 in
            if uu____3115 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3138 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3138 with
         | M t1 ->
             ((let uu____3141 = is_C t1 in
               if uu____3141 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3145) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3151) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3157,uu____3158) -> is_C t1
    | uu____3187 -> false
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
          let uu____3214 =
            let uu____3215 =
              let uu____3225 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3226 =
                let uu____3230 =
                  let uu____3233 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3233) in
                [uu____3230] in
              (uu____3225, uu____3226) in
            FStar_Syntax_Syntax.Tm_app uu____3215 in
          mk1 uu____3214 in
        let uu____3241 =
          let uu____3242 = FStar_Syntax_Syntax.mk_binder p in [uu____3242] in
        let uu____3243 =
          let uu____3250 =
            let uu____3256 =
              let uu____3257 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3257 in
            FStar_Util.Inl uu____3256 in
          Some uu____3250 in
        FStar_Syntax_Util.abs uu____3241 body uu____3243
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___93_3270  ->
    match uu___93_3270 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3271 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
        let return_if uu____3415 =
          match uu____3415 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3436 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3437 =
                       let uu____3438 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3438 in
                     Prims.op_Negation uu____3437) in
                if uu____3436
                then
                  let uu____3439 =
                    let uu____3440 =
                      let uu____3441 = FStar_Syntax_Print.term_to_string e in
                      let uu____3442 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3443 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3441 uu____3442 uu____3443 in
                    FStar_Errors.Err uu____3440 in
                  raise uu____3439
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3457 = mk_return env t1 s_e in
                     ((M t1), uu____3457, u_e)))
               | (M t1,N t2) ->
                   let uu____3460 =
                     let uu____3461 =
                       let uu____3462 = FStar_Syntax_Print.term_to_string e in
                       let uu____3463 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3464 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3462 uu____3463 uu____3464 in
                     FStar_Errors.Err uu____3461 in
                   raise uu____3460) in
        let ensure_m env1 e2 =
          let strip_m uu___94_3490 =
            match uu___94_3490 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3500 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3511 =
                let uu____3512 =
                  let uu____3515 =
                    let uu____3516 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3516 in
                  (uu____3515, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3512 in
              raise uu____3511
          | M uu____3520 ->
              let uu____3521 = check env1 e2 context_nm in strip_m uu____3521 in
        let uu____3525 =
          let uu____3526 = FStar_Syntax_Subst.compress e in
          uu____3526.FStar_Syntax_Syntax.n in
        match uu____3525 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3532 ->
            let uu____3533 = infer env e in return_if uu____3533
        | FStar_Syntax_Syntax.Tm_name uu____3537 ->
            let uu____3538 = infer env e in return_if uu____3538
        | FStar_Syntax_Syntax.Tm_fvar uu____3542 ->
            let uu____3543 = infer env e in return_if uu____3543
        | FStar_Syntax_Syntax.Tm_abs uu____3547 ->
            let uu____3562 = infer env e in return_if uu____3562
        | FStar_Syntax_Syntax.Tm_constant uu____3566 ->
            let uu____3567 = infer env e in return_if uu____3567
        | FStar_Syntax_Syntax.Tm_app uu____3571 ->
            let uu____3581 = infer env e in return_if uu____3581
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3628) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3634) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3640,uu____3641) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3670 ->
            let uu____3678 =
              let uu____3679 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3679 in
            failwith uu____3678
        | FStar_Syntax_Syntax.Tm_type uu____3683 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3687 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3698 ->
            let uu____3703 =
              let uu____3704 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3704 in
            failwith uu____3703
        | FStar_Syntax_Syntax.Tm_uvar uu____3708 ->
            let uu____3717 =
              let uu____3718 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3718 in
            failwith uu____3717
        | FStar_Syntax_Syntax.Tm_delayed uu____3722 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3746 =
              let uu____3747 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3747 in
            failwith uu____3746
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
      let uu____3769 =
        let uu____3770 = FStar_Syntax_Subst.compress e in
        uu____3770.FStar_Syntax_Syntax.n in
      match uu____3769 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___109_3810 = env in
            let uu____3811 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3811;
              subst = (uu___109_3810.subst);
              tc_const = (uu___109_3810.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3820  ->
                 match uu____3820 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___110_3828 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___110_3828.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___110_3828.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3829 =
            FStar_List.fold_left
              (fun uu____3838  ->
                 fun uu____3839  ->
                   match (uu____3838, uu____3839) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3867 = is_C c in
                       if uu____3867
                       then
                         let xw =
                           let uu____3872 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3872 in
                         let x =
                           let uu___111_3874 = bv in
                           let uu____3875 =
                             let uu____3878 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3878 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___111_3874.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___111_3874.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3875
                           } in
                         let env3 =
                           let uu___112_3880 = env2 in
                           let uu____3881 =
                             let uu____3883 =
                               let uu____3884 =
                                 let uu____3889 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3889) in
                               FStar_Syntax_Syntax.NT uu____3884 in
                             uu____3883 :: (env2.subst) in
                           {
                             env = (uu___112_3880.env);
                             subst = uu____3881;
                             tc_const = (uu___112_3880.tc_const)
                           } in
                         let uu____3890 =
                           let uu____3892 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3893 =
                             let uu____3895 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3895 :: acc in
                           uu____3892 :: uu____3893 in
                         (env3, uu____3890)
                       else
                         (let x =
                            let uu___113_3899 = bv in
                            let uu____3900 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___113_3899.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___113_3899.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3900
                            } in
                          let uu____3903 =
                            let uu____3905 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3905 :: acc in
                          (env2, uu____3903))) (env1, []) binders1 in
          (match uu____3829 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3917 =
                 let check_what =
                   let uu____3929 = is_monadic what in
                   if uu____3929 then check_m else check_n in
                 let uu____3938 = check_what env2 body1 in
                 match uu____3938 with
                 | (t,s_body,u_body) ->
                     let uu____3948 =
                       let uu____3949 =
                         let uu____3950 = is_monadic what in
                         if uu____3950 then M t else N t in
                       comp_of_nm uu____3949 in
                     (uu____3948, s_body, u_body) in
               (match uu____3917 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3993 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___95_3995  ->
                                    match uu___95_3995 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3996 -> false)) in
                          if uu____3993
                          then
                            let double_starred_comp =
                              let uu____4004 =
                                let uu____4005 =
                                  let uu____4006 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____4006 in
                                FStar_All.pipe_left double_star uu____4005 in
                              FStar_Syntax_Syntax.mk_Total uu____4004 in
                            let flags =
                              FStar_List.filter
                                (fun uu___96_4011  ->
                                   match uu___96_4011 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____4012 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____4013 =
                              let uu____4019 =
                                let uu____4020 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____4020 in
                              FStar_Util.Inl uu____4019 in
                            Some uu____4013
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___114_4040 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___114_4040.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___114_4040.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___114_4040.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4041  ->
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
                          let uu____4058 =
                            let uu____4064 =
                              let uu____4068 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___97_4070  ->
                                        match uu___97_4070 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4071 -> false)) in
                              if uu____4068
                              then
                                let uu____4075 =
                                  FStar_List.filter
                                    (fun uu___98_4077  ->
                                       match uu___98_4077 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4078 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4075)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4064 in
                          Some uu____4058 in
                    let uu____4090 =
                      let comp1 =
                        let uu____4102 = is_monadic what in
                        let uu____4103 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4102 uu____4103 in
                      let uu____4104 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4104,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4090 with
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
                FStar_Syntax_Syntax.ty = uu____4182;
                FStar_Syntax_Syntax.p = uu____4183;_};
            FStar_Syntax_Syntax.fv_delta = uu____4184;
            FStar_Syntax_Syntax.fv_qual = uu____4185;_}
          ->
          let uu____4191 =
            let uu____4194 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4194 in
          (match uu____4191 with
           | (uu____4210,t) ->
               let uu____4212 = let uu____4213 = normalize1 t in N uu____4213 in
               (uu____4212, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4230 = check_n env head1 in
          (match uu____4230 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4244 =
                   let uu____4245 = FStar_Syntax_Subst.compress t in
                   uu____4245.FStar_Syntax_Syntax.n in
                 match uu____4244 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4248 -> true
                 | uu____4256 -> false in
               let rec flatten1 t =
                 let uu____4268 =
                   let uu____4269 = FStar_Syntax_Subst.compress t in
                   uu____4269.FStar_Syntax_Syntax.n in
                 match uu____4268 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4281);
                                FStar_Syntax_Syntax.tk = uu____4282;
                                FStar_Syntax_Syntax.pos = uu____4283;
                                FStar_Syntax_Syntax.vars = uu____4284;_})
                     when is_arrow t1 ->
                     let uu____4301 = flatten1 t1 in
                     (match uu____4301 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4353,uu____4354)
                     -> flatten1 e1
                 | uu____4383 ->
                     let uu____4384 =
                       let uu____4385 =
                         let uu____4386 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4386 in
                       FStar_Errors.Err uu____4385 in
                     raise uu____4384 in
               let uu____4394 = flatten1 t_head in
               (match uu____4394 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4439 =
                          let uu____4440 =
                            let uu____4441 = FStar_Util.string_of_int n1 in
                            let uu____4445 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4451 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4441 uu____4445 uu____4451 in
                          FStar_Errors.Err uu____4440 in
                        raise uu____4439)
                     else ();
                     (let uu____4456 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4456 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4483 args1 =
                            match uu____4483 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4526 =
                                       let uu____4527 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4527.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4526
                                 | (binders3,[]) ->
                                     let uu____4546 =
                                       let uu____4547 =
                                         let uu____4550 =
                                           let uu____4551 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4551 in
                                         FStar_Syntax_Subst.compress
                                           uu____4550 in
                                       uu____4547.FStar_Syntax_Syntax.n in
                                     (match uu____4546 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4567 =
                                            let uu____4568 =
                                              let uu____4569 =
                                                let uu____4577 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4577) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4569 in
                                            mk1 uu____4568 in
                                          N uu____4567
                                      | uu____4581 -> failwith "wat?")
                                 | ([],uu____4582::uu____4583) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4608)::binders3,(arg,uu____4611)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4645 = FStar_List.splitAt n' binders1 in
                          (match uu____4645 with
                           | (binders2,uu____4662) ->
                               let uu____4675 =
                                 let uu____4685 =
                                   FStar_List.map2
                                     (fun uu____4705  ->
                                        fun uu____4706  ->
                                          match (uu____4705, uu____4706) with
                                          | ((bv,uu____4723),(arg,q)) ->
                                              let uu____4730 =
                                                let uu____4731 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4731.FStar_Syntax_Syntax.n in
                                              (match uu____4730 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4741 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4754 ->
                                                   let uu____4755 =
                                                     check_n env arg in
                                                   (match uu____4755 with
                                                    | (uu____4766,s_arg,u_arg)
                                                        ->
                                                        let uu____4769 =
                                                          let uu____4773 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4773
                                                          then
                                                            let uu____4777 =
                                                              let uu____4780
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4780, q) in
                                                            [uu____4777;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4769))))
                                     binders2 args in
                                 FStar_List.split uu____4685 in
                               (match uu____4675 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4827 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4833 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4827, uu____4833)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4882) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4888) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4894,uu____4895) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4925 = let uu____4926 = env.tc_const c in N uu____4926 in
          (uu____4925, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4927 ->
          let uu____4935 =
            let uu____4936 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4936 in
          failwith uu____4935
      | FStar_Syntax_Syntax.Tm_type uu____4940 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4944 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4955 ->
          let uu____4960 =
            let uu____4961 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4961 in
          failwith uu____4960
      | FStar_Syntax_Syntax.Tm_uvar uu____4965 ->
          let uu____4974 =
            let uu____4975 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4975 in
          failwith uu____4974
      | FStar_Syntax_Syntax.Tm_delayed uu____4979 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5003 =
            let uu____5004 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____5004 in
          failwith uu____5003
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
          let uu____5042 = check_n env e0 in
          match uu____5042 with
          | (uu____5049,s_e0,u_e0) ->
              let uu____5052 =
                let uu____5070 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5103 = FStar_Syntax_Subst.open_branch b in
                       match uu____5103 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___115_5135 = env in
                             let uu____5136 =
                               let uu____5137 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5137 in
                             {
                               env = uu____5136;
                               subst = (uu___115_5135.subst);
                               tc_const = (uu___115_5135.tc_const)
                             } in
                           let uu____5139 = f env1 body in
                           (match uu____5139 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5188 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5070 in
              (match uu____5052 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5253 = FStar_List.hd nms in
                     match uu____5253 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___99_5257  ->
                          match uu___99_5257 with
                          | M uu____5258 -> true
                          | uu____5259 -> false) nms in
                   let uu____5260 =
                     let uu____5283 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5335  ->
                              match uu____5335 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5458 =
                                         check env original_body (M t2) in
                                       (match uu____5458 with
                                        | (uu____5481,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5510,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5283 in
                   (match uu____5260 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5629  ->
                                 match uu____5629 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5670 =
                                         let uu____5671 =
                                           let uu____5681 =
                                             let uu____5685 =
                                               let uu____5688 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5689 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5688, uu____5689) in
                                             [uu____5685] in
                                           (s_body, uu____5681) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5671 in
                                       mk1 uu____5670 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5711 =
                              let uu____5712 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5712] in
                            let uu____5713 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5715 =
                              let uu____5722 =
                                let uu____5728 =
                                  let uu____5729 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5729 in
                                FStar_Util.Inl uu____5728 in
                              Some uu____5722 in
                            FStar_Syntax_Util.abs uu____5711 uu____5713
                              uu____5715 in
                          let t1_star =
                            let uu____5743 =
                              let uu____5747 =
                                let uu____5748 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5748 in
                              [uu____5747] in
                            let uu____5749 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5743 uu____5749 in
                          let uu____5752 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5782 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5752, uu____5782)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5796 =
                             let uu____5799 =
                               let uu____5800 =
                                 let uu____5818 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5818,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5800 in
                             mk1 uu____5799 in
                           let uu____5845 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5796, uu____5845))))
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
              let uu____5888 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5888] in
            let uu____5889 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5889 with
            | (x_binders1,e21) ->
                let uu____5897 = infer env e1 in
                (match uu____5897 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5908 = is_C t1 in
                       if uu____5908
                       then
                         let uu___116_5909 = binding in
                         let uu____5910 =
                           let uu____5913 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5913 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___116_5909.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___116_5909.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5910;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___116_5909.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___116_5909.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___117_5916 = env in
                       let uu____5917 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___118_5918 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___118_5918.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___118_5918.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5917;
                         subst = (uu___117_5916.subst);
                         tc_const = (uu___117_5916.tc_const)
                       } in
                     let uu____5919 = proceed env1 e21 in
                     (match uu____5919 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___119_5930 = binding in
                            let uu____5931 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___119_5930.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___119_5930.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5931;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___119_5930.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___119_5930.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5934 =
                            let uu____5937 =
                              let uu____5938 =
                                let uu____5946 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___120_5951 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___120_5951.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___120_5951.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___120_5951.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___120_5951.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5946) in
                              FStar_Syntax_Syntax.Tm_let uu____5938 in
                            mk1 uu____5937 in
                          let uu____5952 =
                            let uu____5955 =
                              let uu____5956 =
                                let uu____5964 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___121_5969 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5969.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5969.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5969.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5969.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5964) in
                              FStar_Syntax_Syntax.Tm_let uu____5956 in
                            mk1 uu____5955 in
                          (nm_rec, uu____5934, uu____5952))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___122_5978 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___122_5978.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___122_5978.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___122_5978.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___123_5980 = env in
                       let uu____5981 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___124_5982 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_5982.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_5982.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5981;
                         subst = (uu___123_5980.subst);
                         tc_const = (uu___123_5980.tc_const)
                       } in
                     let uu____5983 = ensure_m env1 e21 in
                     (match uu____5983 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____6000 =
                              let uu____6001 =
                                let uu____6011 =
                                  let uu____6015 =
                                    let uu____6018 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6019 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6018, uu____6019) in
                                  [uu____6015] in
                                (s_e2, uu____6011) in
                              FStar_Syntax_Syntax.Tm_app uu____6001 in
                            mk1 uu____6000 in
                          let s_e22 =
                            let uu____6028 =
                              let uu____6035 =
                                let uu____6041 =
                                  let uu____6042 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6042 in
                                FStar_Util.Inl uu____6041 in
                              Some uu____6035 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6028 in
                          let body =
                            let uu____6056 =
                              let uu____6057 =
                                let uu____6067 =
                                  let uu____6071 =
                                    let uu____6074 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6074) in
                                  [uu____6071] in
                                (s_e1, uu____6067) in
                              FStar_Syntax_Syntax.Tm_app uu____6057 in
                            mk1 uu____6056 in
                          let uu____6082 =
                            let uu____6083 =
                              let uu____6084 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6084] in
                            let uu____6085 =
                              let uu____6092 =
                                let uu____6098 =
                                  let uu____6099 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6099 in
                                FStar_Util.Inl uu____6098 in
                              Some uu____6092 in
                            FStar_Syntax_Util.abs uu____6083 body uu____6085 in
                          let uu____6110 =
                            let uu____6113 =
                              let uu____6114 =
                                let uu____6122 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___125_6127 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_6127.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_6127.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_6127.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_6127.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6122) in
                              FStar_Syntax_Syntax.Tm_let uu____6114 in
                            mk1 uu____6113 in
                          ((M t2), uu____6082, uu____6110)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6136 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6136 in
      let uu____6141 = check env e mn in
      match uu____6141 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6151 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6164 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6164 in
      let uu____6169 = check env e mn in
      match uu____6169 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6179 -> failwith "[check_m]: impossible"
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
        (let uu____6201 =
           let uu____6202 = is_C c in Prims.op_Negation uu____6202 in
         if uu____6201 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6214 =
           let uu____6215 = FStar_Syntax_Subst.compress c in
           uu____6215.FStar_Syntax_Syntax.n in
         match uu____6214 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6234 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6234 with
              | (wp_head,wp_args) ->
                  ((let uu____6261 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6274 =
                           let uu____6275 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6275 in
                         Prims.op_Negation uu____6274) in
                    if uu____6261 then failwith "mismatch" else ());
                   (let uu____6284 =
                      let uu____6285 =
                        let uu____6295 =
                          FStar_List.map2
                            (fun uu____6305  ->
                               fun uu____6306  ->
                                 match (uu____6305, uu____6306) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6329 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6329
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6332 = print_implicit q in
                                         let uu____6333 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6332 uu____6333)
                                      else ();
                                      (let uu____6335 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6335, q)))) args wp_args in
                        (head1, uu____6295) in
                      FStar_Syntax_Syntax.Tm_app uu____6285 in
                    mk1 uu____6284)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6357 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6357 with
              | (binders_orig,comp1) ->
                  let uu____6362 =
                    let uu____6370 =
                      FStar_List.map
                        (fun uu____6384  ->
                           match uu____6384 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6397 = is_C h in
                               if uu____6397
                               then
                                 let w' =
                                   let uu____6404 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6404 in
                                 let uu____6405 =
                                   let uu____6409 =
                                     let uu____6413 =
                                       let uu____6416 =
                                         let uu____6417 =
                                           let uu____6418 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6418 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6417 in
                                       (uu____6416, q) in
                                     [uu____6413] in
                                   (w', q) :: uu____6409 in
                                 (w', uu____6405)
                               else
                                 (let x =
                                    let uu____6430 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6430 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6370 in
                  (match uu____6362 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6460 =
                           let uu____6462 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6462 in
                         FStar_Syntax_Subst.subst_comp uu____6460 comp1 in
                       let app =
                         let uu____6466 =
                           let uu____6467 =
                             let uu____6477 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6484 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6485 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6484, uu____6485)) bvs in
                             (wp, uu____6477) in
                           FStar_Syntax_Syntax.Tm_app uu____6467 in
                         mk1 uu____6466 in
                       let comp3 =
                         let uu____6490 = type_of_comp comp2 in
                         let uu____6491 = is_monadic_comp comp2 in
                         trans_G env uu____6490 uu____6491 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6493,uu____6494) ->
             trans_F_ env e wp
         | uu____6523 -> failwith "impossible trans_F_")
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
            let uu____6538 =
              let uu____6539 = star_type' env h in
              let uu____6542 =
                let uu____6548 =
                  let uu____6551 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6551) in
                [uu____6548] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6539;
                FStar_Syntax_Syntax.effect_args = uu____6542;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6538
          else
            (let uu____6557 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6557)
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
    fun t  -> let uu____6568 = n env.env t in star_type' env uu____6568
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6580 = n env.env t in check_n env uu____6580
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6590 = n env.env c in
        let uu____6591 = n env.env wp in trans_F_ env uu____6590 uu____6591