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
              let uu___103_64 = a in
              let uu____65 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___103_64.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___103_64.FStar_Syntax_Syntax.index);
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
                     ((Prims.fst t), uu____239)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____252 =
                       FStar_Syntax_Syntax.bv_to_name (Prims.fst bv) in
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
                                      FStar_Syntax_Syntax.GTotal (b,_);
                                    FStar_Syntax_Syntax.tk = _;
                                    FStar_Syntax_Syntax.pos = _;
                                    FStar_Syntax_Syntax.vars = _;_})
                      |FStar_Syntax_Syntax.Tm_arrow
                      (binder::[],{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Total (b,_);
                                    FStar_Syntax_Syntax.tk = _;
                                    FStar_Syntax_Syntax.pos = _;
                                    FStar_Syntax_Syntax.vars = _;_})
                        ->
                        let a2 = (Prims.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1479 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1479
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1482 =
                              let uu____1485 =
                                let uu____1491 =
                                  let uu____1492 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1492 in
                                [uu____1491] in
                              FStar_Syntax_Util.mk_app x uu____1485 in
                            let uu____1493 =
                              let uu____1496 =
                                let uu____1502 =
                                  let uu____1503 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1503 in
                                [uu____1502] in
                              FStar_Syntax_Util.mk_app y uu____1496 in
                            mk_rel1 b uu____1482 uu____1493 in
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
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___104_1561 = t1 in
                          let uu____1562 =
                            let uu____1563 =
                              let uu____1571 =
                                let uu____1572 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1572 in
                              ([binder], uu____1571) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1563 in
                          {
                            FStar_Syntax_Syntax.n = uu____1562;
                            FStar_Syntax_Syntax.tk =
                              (uu___104_1561.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___104_1561.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___104_1561.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1584 ->
                        failwith "unhandled arrow"
                    | uu____1592 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1609 =
                        let uu____1610 = FStar_Syntax_Subst.compress t1 in
                        uu____1610.FStar_Syntax_Syntax.n in
                      match uu____1609 with
                      | FStar_Syntax_Syntax.Tm_type uu____1615 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1632 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1632
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1647 =
                                let uu____1648 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1648 i in
                              FStar_Syntax_Syntax.fvar uu____1647
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1669 =
                            let uu____1677 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1686  ->
                                     match uu____1686 with
                                     | (t2,q) ->
                                         let uu____1693 = project i x in
                                         let uu____1694 = project i y in
                                         mk_stronger t2 uu____1693 uu____1694)
                                args in
                            match uu____1677 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1669 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                        (binders1,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.GTotal (b,_);
                                    FStar_Syntax_Syntax.tk = _;
                                    FStar_Syntax_Syntax.pos = _;
                                    FStar_Syntax_Syntax.vars = _;_})
                        |FStar_Syntax_Syntax.Tm_arrow
                        (binders1,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Total (b,_);
                                    FStar_Syntax_Syntax.tk = _;
                                    FStar_Syntax_Syntax.pos = _;
                                    FStar_Syntax_Syntax.vars = _;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1780  ->
                                   match uu____1780 with
                                   | (bv,q) ->
                                       let uu____1785 =
                                         let uu____1786 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1786 in
                                       FStar_Syntax_Syntax.gen_bv uu____1785
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1790 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1790) bvs in
                          let body =
                            let uu____1794 = FStar_Syntax_Util.mk_app x args in
                            let uu____1795 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1794 uu____1795 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1798 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1804 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1805 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1806 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1804 uu____1805 uu____1806 in
                    let uu____1807 =
                      let uu____1808 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1808 in
                    FStar_Syntax_Util.abs uu____1807 body ret_tot_type in
                  let stronger1 =
                    let uu____1823 = mk_lid "stronger" in
                    register env1 uu____1823 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1829 = FStar_Util.prefix gamma in
                    match uu____1829 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (Prims.fst post).FStar_Syntax_Syntax.sort in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1855 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1855 in
                          let uu____1858 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1858 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1866 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1866 in
                              let guard_free1 =
                                let uu____1873 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1873 in
                              let pat =
                                let uu____1877 =
                                  let uu____1883 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1883] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1877 in
                              let pattern_guarded_body =
                                let uu____1887 =
                                  let uu____1888 =
                                    let uu____1893 =
                                      let uu____1894 =
                                        let uu____1901 =
                                          let uu____1903 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1903] in
                                        [uu____1901] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1894 in
                                    (body, uu____1893) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1888 in
                                mk1 uu____1887 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1906 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1909 =
                            let uu____1910 =
                              let uu____1911 =
                                let uu____1912 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1915 =
                                  let uu____1921 = args_of_binders1 wp_args in
                                  let uu____1923 =
                                    let uu____1925 =
                                      let uu____1926 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1926 in
                                    [uu____1925] in
                                  FStar_List.append uu____1921 uu____1923 in
                                FStar_Syntax_Util.mk_app uu____1912
                                  uu____1915 in
                              FStar_Syntax_Util.mk_imp equiv uu____1911 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1910 in
                          FStar_Syntax_Util.abs gamma uu____1909
                            ret_gtot_type in
                        let uu____1927 =
                          let uu____1928 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1928 in
                        FStar_Syntax_Util.abs uu____1927 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1935 = mk_lid "wp_ite" in
                    register env1 uu____1935 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1941 = FStar_Util.prefix gamma in
                    match uu____1941 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1965 =
                            let uu____1966 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (Prims.fst post) in
                            let uu____1969 =
                              let uu____1975 =
                                let uu____1976 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1976 in
                              [uu____1975] in
                            FStar_Syntax_Util.mk_app uu____1966 uu____1969 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1965 in
                        let uu____1977 =
                          let uu____1978 =
                            let uu____1982 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1982 gamma in
                          FStar_List.append binders uu____1978 in
                        FStar_Syntax_Util.abs uu____1977 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1991 = mk_lid "null_wp" in
                    register env1 uu____1991 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2000 =
                        let uu____2006 =
                          let uu____2008 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2009 =
                            let uu____2011 =
                              let uu____2014 =
                                let uu____2020 =
                                  let uu____2021 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2021 in
                                [uu____2020] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2014 in
                            let uu____2022 =
                              let uu____2026 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2026] in
                            uu____2011 :: uu____2022 in
                          uu____2008 :: uu____2009 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2006 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2000 in
                    let uu____2029 =
                      let uu____2030 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2030 in
                    FStar_Syntax_Util.abs uu____2029 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2037 = mk_lid "wp_trivial" in
                    register env1 uu____2037 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2042 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2042
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2047 =
                      let uu____2049 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2049 in
                    let uu____2054 =
                      let uu___105_2055 = ed in
                      let uu____2056 =
                        let uu____2057 = c wp_if_then_else2 in
                        ([], uu____2057) in
                      let uu____2059 =
                        let uu____2060 = c wp_ite2 in ([], uu____2060) in
                      let uu____2062 =
                        let uu____2063 = c stronger2 in ([], uu____2063) in
                      let uu____2065 =
                        let uu____2066 = c wp_close2 in ([], uu____2066) in
                      let uu____2068 =
                        let uu____2069 = c wp_assert2 in ([], uu____2069) in
                      let uu____2071 =
                        let uu____2072 = c wp_assume2 in ([], uu____2072) in
                      let uu____2074 =
                        let uu____2075 = c null_wp2 in ([], uu____2075) in
                      let uu____2077 =
                        let uu____2078 = c wp_trivial2 in ([], uu____2078) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___105_2055.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___105_2055.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___105_2055.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___105_2055.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___105_2055.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___105_2055.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___105_2055.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2056;
                        FStar_Syntax_Syntax.ite_wp = uu____2059;
                        FStar_Syntax_Syntax.stronger = uu____2062;
                        FStar_Syntax_Syntax.close_wp = uu____2065;
                        FStar_Syntax_Syntax.assert_p = uu____2068;
                        FStar_Syntax_Syntax.assume_p = uu____2071;
                        FStar_Syntax_Syntax.null_wp = uu____2074;
                        FStar_Syntax_Syntax.trivial = uu____2077;
                        FStar_Syntax_Syntax.repr =
                          (uu___105_2055.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___105_2055.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___105_2055.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___105_2055.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2047, uu____2054)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___106_2090 = dmff_env in
      {
        env = env';
        subst = (uu___106_2090.subst);
        tc_const = (uu___106_2090.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2101 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2113 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___92_2123  ->
    match uu___92_2123 with
    | FStar_Syntax_Syntax.Total (t,uu____2125) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___91_2134  ->
                match uu___91_2134 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2135 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2137 =
          let uu____2138 =
            let uu____2139 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2139 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2138 in
        failwith uu____2137
    | FStar_Syntax_Syntax.GTotal uu____2140 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___93_2148  ->
    match uu___93_2148 with
    | N t ->
        let uu____2150 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2150
    | M t ->
        let uu____2152 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2152
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2156,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2158;
                      FStar_Syntax_Syntax.pos = uu____2159;
                      FStar_Syntax_Syntax.vars = uu____2160;_})
        -> nm_of_comp n2
    | uu____2171 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2183 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2183 with | M uu____2184 -> true | N uu____2185 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2189 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2199 =
        let uu____2203 =
          let uu____2204 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2204 in
        [uu____2203] in
      let uu____2205 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2199 uu____2205 in
    let uu____2208 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2208
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
          (let uu____2243 =
             let uu____2251 =
               let uu____2255 =
                 let uu____2258 =
                   let uu____2259 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2259 in
                 let uu____2260 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2258, uu____2260) in
               [uu____2255] in
             let uu____2265 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2251, uu____2265) in
           FStar_Syntax_Syntax.Tm_arrow uu____2243)
and star_type':
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk1 x = (FStar_Syntax_Syntax.mk x) None t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk1 in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2298) ->
          let binders1 =
            FStar_List.map
              (fun uu____2317  ->
                 match uu____2317 with
                 | (bv,aqual) ->
                     let uu____2324 =
                       let uu___107_2325 = bv in
                       let uu____2326 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___107_2325.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___107_2325.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2326
                       } in
                     (uu____2324, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2329,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2331);
                             FStar_Syntax_Syntax.tk = uu____2332;
                             FStar_Syntax_Syntax.pos = uu____2333;
                             FStar_Syntax_Syntax.vars = uu____2334;_})
               ->
               let uu____2351 =
                 let uu____2352 =
                   let uu____2360 =
                     let uu____2361 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2361 in
                   (binders1, uu____2360) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2352 in
               mk1 uu____2351
           | uu____2365 ->
               let uu____2366 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2366 with
                | N hn ->
                    let uu____2368 =
                      let uu____2369 =
                        let uu____2377 =
                          let uu____2378 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2378 in
                        (binders1, uu____2377) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2369 in
                    mk1 uu____2368
                | M a ->
                    let uu____2383 =
                      let uu____2384 =
                        let uu____2392 =
                          let uu____2396 =
                            let uu____2400 =
                              let uu____2403 =
                                let uu____2404 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2404 in
                              let uu____2405 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2403, uu____2405) in
                            [uu____2400] in
                          FStar_List.append binders1 uu____2396 in
                        let uu____2412 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2392, uu____2412) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2384 in
                    mk1 uu____2383))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2463 = f x in
                    FStar_Util.string_builder_append strb uu____2463);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2467 = f x1 in
                         FStar_Util.string_builder_append strb uu____2467))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2469 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2470 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2469 uu____2470 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2478 =
              let uu____2479 = FStar_Syntax_Subst.compress ty in
              uu____2479.FStar_Syntax_Syntax.n in
            match uu____2478 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2494 =
                  let uu____2495 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2495 in
                if uu____2494
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2509 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2509 s in
                       let uu____2511 =
                         let uu____2512 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2512 in
                       if uu____2511
                       then (debug1 ty1 sinter; Prims.raise Not_found)
                       else () in
                     let uu____2515 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2515 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2526  ->
                                  match uu____2526 with
                                  | (bv,uu____2532) ->
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
            | uu____2545 ->
                ((let uu____2547 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2547);
                 false) in
          let rec is_valid_application head2 =
            let uu____2552 =
              let uu____2553 = FStar_Syntax_Subst.compress head2 in
              uu____2553.FStar_Syntax_Syntax.n in
            match uu____2552 with
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
                  (let uu____2557 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2557)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2570 -> true
                 | uu____2580 ->
                     ((let uu____2582 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2582);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
                true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2586) ->
                is_valid_application t2
            | uu____2591 -> false in
          let uu____2592 = is_valid_application head1 in
          if uu____2592
          then
            let uu____2593 =
              let uu____2594 =
                let uu____2604 =
                  FStar_List.map
                    (fun uu____2614  ->
                       match uu____2614 with
                       | (t2,qual) ->
                           let uu____2627 = star_type' env t2 in
                           (uu____2627, qual)) args in
                (head1, uu____2604) in
              FStar_Syntax_Syntax.Tm_app uu____2594 in
            mk1 uu____2593
          else
            (let uu____2634 =
               let uu____2635 =
                 let uu____2636 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2636 in
               FStar_Errors.Err uu____2635 in
             Prims.raise uu____2634)
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_name _
         |FStar_Syntax_Syntax.Tm_type _|FStar_Syntax_Syntax.Tm_fvar _ -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2666 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2666 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___110_2672 = env in
                 let uu____2673 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2673;
                   subst = (uu___110_2672.subst);
                   tc_const = (uu___110_2672.tc_const)
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
               ((let uu___111_2690 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___111_2690.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___111_2690.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2697 =
            let uu____2698 =
              let uu____2703 = star_type' env t2 in (uu____2703, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2698 in
          mk1 uu____2697
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2741 =
            let uu____2742 =
              let uu____2760 = star_type' env e in
              let uu____2761 =
                let uu____2771 =
                  let uu____2776 = star_type' env t2 in
                  FStar_Util.Inl uu____2776 in
                (uu____2771, None) in
              (uu____2760, uu____2761, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2742 in
          mk1 uu____2741
      | FStar_Syntax_Syntax.Tm_ascribed uu____2798 ->
          let uu____2816 =
            let uu____2817 =
              let uu____2818 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2818 in
            FStar_Errors.Err uu____2817 in
          Prims.raise uu____2816
      | FStar_Syntax_Syntax.Tm_refine uu____2819 ->
          let uu____2824 =
            let uu____2825 =
              let uu____2826 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2826 in
            FStar_Errors.Err uu____2825 in
          Prims.raise uu____2824
      | FStar_Syntax_Syntax.Tm_uinst uu____2827 ->
          let uu____2832 =
            let uu____2833 =
              let uu____2834 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2834 in
            FStar_Errors.Err uu____2833 in
          Prims.raise uu____2832
      | FStar_Syntax_Syntax.Tm_constant uu____2835 ->
          let uu____2836 =
            let uu____2837 =
              let uu____2838 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2838 in
            FStar_Errors.Err uu____2837 in
          Prims.raise uu____2836
      | FStar_Syntax_Syntax.Tm_match uu____2839 ->
          let uu____2855 =
            let uu____2856 =
              let uu____2857 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2857 in
            FStar_Errors.Err uu____2856 in
          Prims.raise uu____2855
      | FStar_Syntax_Syntax.Tm_let uu____2858 ->
          let uu____2866 =
            let uu____2867 =
              let uu____2868 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2868 in
            FStar_Errors.Err uu____2867 in
          Prims.raise uu____2866
      | FStar_Syntax_Syntax.Tm_uvar uu____2869 ->
          let uu____2878 =
            let uu____2879 =
              let uu____2880 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2880 in
            FStar_Errors.Err uu____2879 in
          Prims.raise uu____2878
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2881 =
            let uu____2882 =
              let uu____2883 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2883 in
            FStar_Errors.Err uu____2882 in
          Prims.raise uu____2881
      | FStar_Syntax_Syntax.Tm_delayed uu____2884 -> failwith "impossible"
let is_monadic uu___95_2917 =
  match uu___95_2917 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
    { FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _;
      FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _;_})
    |Some (FStar_Util.Inr (_,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___94_2954  ->
              match uu___94_2954 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____2955 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2959 =
      let uu____2960 = FStar_Syntax_Subst.compress t in
      uu____2960.FStar_Syntax_Syntax.n in
    match uu____2959 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2980 =
            let uu____2981 = FStar_List.hd args in Prims.fst uu____2981 in
          is_C uu____2980 in
        if r
        then
          ((let uu____2993 =
              let uu____2994 =
                FStar_List.for_all
                  (fun uu____2997  ->
                     match uu____2997 with | (h,uu____3001) -> is_C h) args in
              Prims.op_Negation uu____2994 in
            if uu____2993 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3005 =
              let uu____3006 =
                FStar_List.for_all
                  (fun uu____3009  ->
                     match uu____3009 with
                     | (h,uu____3013) ->
                         let uu____3014 = is_C h in
                         Prims.op_Negation uu____3014) args in
              Prims.op_Negation uu____3006 in
            if uu____3005 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3028 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3028 with
         | M t1 ->
             ((let uu____3031 = is_C t1 in
               if uu____3031 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,_)
      |FStar_Syntax_Syntax.Tm_uinst (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
       (t1,_,_) -> is_C t1
    | uu____3063 -> false
let mk_return:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x = (FStar_Syntax_Syntax.mk x) None e.FStar_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk1 env t in
        let p = FStar_Syntax_Syntax.gen_bv "p'" None p_type in
        let body =
          let uu____3094 =
            let uu____3095 =
              let uu____3105 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3106 =
                let uu____3110 =
                  let uu____3113 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3113) in
                [uu____3110] in
              (uu____3105, uu____3106) in
            FStar_Syntax_Syntax.Tm_app uu____3095 in
          mk1 uu____3094 in
        let uu____3121 =
          let uu____3122 = FStar_Syntax_Syntax.mk_binder p in [uu____3122] in
        let uu____3123 =
          let uu____3130 =
            let uu____3136 =
              let uu____3137 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3137 in
            FStar_Util.Inl uu____3136 in
          Some uu____3130 in
        FStar_Syntax_Util.abs uu____3121 body uu____3123
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___96_3150  ->
    match uu___96_3150 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3151 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
        let return_if uu____3295 =
          match uu____3295 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3316 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3317 =
                       let uu____3318 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3318 in
                     Prims.op_Negation uu____3317) in
                if uu____3316
                then
                  let uu____3319 =
                    let uu____3320 =
                      let uu____3321 = FStar_Syntax_Print.term_to_string e in
                      let uu____3322 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3323 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3321 uu____3322 uu____3323 in
                    FStar_Errors.Err uu____3320 in
                  Prims.raise uu____3319
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2)|(M t1,M t2) ->
                   (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3334 = mk_return env t1 s_e in
                     ((M t1), uu____3334, u_e)))
               | (M t1,N t2) ->
                   let uu____3337 =
                     let uu____3338 =
                       let uu____3339 = FStar_Syntax_Print.term_to_string e in
                       let uu____3340 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3341 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3339 uu____3340 uu____3341 in
                     FStar_Errors.Err uu____3338 in
                   Prims.raise uu____3337) in
        let ensure_m env1 e2 =
          let strip_m uu___97_3367 =
            match uu___97_3367 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3377 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3388 =
                let uu____3389 =
                  let uu____3392 =
                    let uu____3393 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3393 in
                  (uu____3392, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3389 in
              Prims.raise uu____3388
          | M uu____3397 ->
              let uu____3398 = check env1 e2 context_nm in strip_m uu____3398 in
        let uu____3402 =
          let uu____3403 = FStar_Syntax_Subst.compress e in
          uu____3403.FStar_Syntax_Syntax.n in
        match uu____3402 with
        | FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_name _
           |FStar_Syntax_Syntax.Tm_fvar _
            |FStar_Syntax_Syntax.Tm_abs _
             |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_app _
            -> let uu____3415 = infer env e in return_if uu____3415
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,_)
          |FStar_Syntax_Syntax.Tm_uinst (e1,_)
           |FStar_Syntax_Syntax.Tm_ascribed (e1,_,_) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3490 ->
            let uu____3498 =
              let uu____3499 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3499 in
            failwith uu____3498
        | FStar_Syntax_Syntax.Tm_type uu____3503 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3507 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3518 ->
            let uu____3523 =
              let uu____3524 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3524 in
            failwith uu____3523
        | FStar_Syntax_Syntax.Tm_uvar uu____3528 ->
            let uu____3537 =
              let uu____3538 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3538 in
            failwith uu____3537
        | FStar_Syntax_Syntax.Tm_delayed uu____3542 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3566 =
              let uu____3567 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3567 in
            failwith uu____3566
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
      let uu____3589 =
        let uu____3590 = FStar_Syntax_Subst.compress e in
        uu____3590.FStar_Syntax_Syntax.n in
      match uu____3589 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___112_3630 = env in
            let uu____3631 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3631;
              subst = (uu___112_3630.subst);
              tc_const = (uu___112_3630.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3640  ->
                 match uu____3640 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_3648 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_3648.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_3648.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3649 =
            FStar_List.fold_left
              (fun uu____3658  ->
                 fun uu____3659  ->
                   match (uu____3658, uu____3659) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3687 = is_C c in
                       if uu____3687
                       then
                         let xw =
                           let uu____3692 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3692 in
                         let x =
                           let uu___114_3694 = bv in
                           let uu____3695 =
                             let uu____3698 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3698 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_3694.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_3694.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3695
                           } in
                         let env3 =
                           let uu___115_3700 = env2 in
                           let uu____3701 =
                             let uu____3703 =
                               let uu____3704 =
                                 let uu____3709 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3709) in
                               FStar_Syntax_Syntax.NT uu____3704 in
                             uu____3703 :: (env2.subst) in
                           {
                             env = (uu___115_3700.env);
                             subst = uu____3701;
                             tc_const = (uu___115_3700.tc_const)
                           } in
                         let uu____3710 =
                           let uu____3712 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3713 =
                             let uu____3715 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3715 :: acc in
                           uu____3712 :: uu____3713 in
                         (env3, uu____3710)
                       else
                         (let x =
                            let uu___116_3719 = bv in
                            let uu____3720 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_3719.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_3719.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3720
                            } in
                          let uu____3723 =
                            let uu____3725 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3725 :: acc in
                          (env2, uu____3723))) (env1, []) binders1 in
          (match uu____3649 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3737 =
                 let check_what =
                   let uu____3749 = is_monadic what in
                   if uu____3749 then check_m else check_n in
                 let uu____3758 = check_what env2 body1 in
                 match uu____3758 with
                 | (t,s_body,u_body) ->
                     let uu____3768 =
                       let uu____3769 =
                         let uu____3770 = is_monadic what in
                         if uu____3770 then M t else N t in
                       comp_of_nm uu____3769 in
                     (uu____3768, s_body, u_body) in
               (match uu____3737 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3813 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___98_3815  ->
                                    match uu___98_3815 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3816 -> false)) in
                          if uu____3813
                          then
                            let double_starred_comp =
                              let uu____3824 =
                                let uu____3825 =
                                  let uu____3826 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____3826 in
                                FStar_All.pipe_left double_star uu____3825 in
                              FStar_Syntax_Syntax.mk_Total uu____3824 in
                            let flags =
                              FStar_List.filter
                                (fun uu___99_3831  ->
                                   match uu___99_3831 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3832 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____3833 =
                              let uu____3839 =
                                let uu____3840 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____3840 in
                              FStar_Util.Inl uu____3839 in
                            Some uu____3833
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___117_3860 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___117_3860.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___117_3860.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___117_3860.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____3861  ->
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
                          let uu____3878 =
                            let uu____3884 =
                              let uu____3888 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___100_3890  ->
                                        match uu___100_3890 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____3891 -> false)) in
                              if uu____3888
                              then
                                let uu____3895 =
                                  FStar_List.filter
                                    (fun uu___101_3897  ->
                                       match uu___101_3897 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____3898 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____3895)
                              else (lid, flags) in
                            FStar_Util.Inr uu____3884 in
                          Some uu____3878 in
                    let uu____3910 =
                      let comp1 =
                        let uu____3922 = is_monadic what in
                        let uu____3923 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3922 uu____3923 in
                      let uu____3924 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____3924,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____3910 with
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
                FStar_Syntax_Syntax.ty = uu____4002;
                FStar_Syntax_Syntax.p = uu____4003;_};
            FStar_Syntax_Syntax.fv_delta = uu____4004;
            FStar_Syntax_Syntax.fv_qual = uu____4005;_}
          ->
          let uu____4011 =
            let uu____4014 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left Prims.fst uu____4014 in
          (match uu____4011 with
           | (uu____4030,t) ->
               let uu____4032 = let uu____4033 = normalize1 t in N uu____4033 in
               (uu____4032, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4050 = check_n env head1 in
          (match uu____4050 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4064 =
                   let uu____4065 = FStar_Syntax_Subst.compress t in
                   uu____4065.FStar_Syntax_Syntax.n in
                 match uu____4064 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4068 -> true
                 | uu____4076 -> false in
               let rec flatten1 t =
                 let uu____4088 =
                   let uu____4089 = FStar_Syntax_Subst.compress t in
                   uu____4089.FStar_Syntax_Syntax.n in
                 match uu____4088 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4101);
                                FStar_Syntax_Syntax.tk = uu____4102;
                                FStar_Syntax_Syntax.pos = uu____4103;
                                FStar_Syntax_Syntax.vars = uu____4104;_})
                     when is_arrow t1 ->
                     let uu____4121 = flatten1 t1 in
                     (match uu____4121 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4173,uu____4174)
                     -> flatten1 e1
                 | uu____4203 ->
                     let uu____4204 =
                       let uu____4205 =
                         let uu____4206 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4206 in
                       FStar_Errors.Err uu____4205 in
                     Prims.raise uu____4204 in
               let uu____4214 = flatten1 t_head in
               (match uu____4214 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4259 =
                          let uu____4260 =
                            let uu____4261 = FStar_Util.string_of_int n1 in
                            let uu____4265 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4271 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4261 uu____4265 uu____4271 in
                          FStar_Errors.Err uu____4260 in
                        Prims.raise uu____4259)
                     else ();
                     (let uu____4276 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4276 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4303 args1 =
                            match uu____4303 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4346 =
                                       let uu____4347 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4347.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4346
                                 | (binders3,[]) ->
                                     let uu____4366 =
                                       let uu____4367 =
                                         let uu____4370 =
                                           let uu____4371 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4371 in
                                         FStar_Syntax_Subst.compress
                                           uu____4370 in
                                       uu____4367.FStar_Syntax_Syntax.n in
                                     (match uu____4366 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4387 =
                                            let uu____4388 =
                                              let uu____4389 =
                                                let uu____4397 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4397) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4389 in
                                            mk1 uu____4388 in
                                          N uu____4387
                                      | uu____4401 -> failwith "wat?")
                                 | ([],uu____4402::uu____4403) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4428)::binders3,(arg,uu____4431)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4465 = FStar_List.splitAt n' binders1 in
                          (match uu____4465 with
                           | (binders2,uu____4482) ->
                               let uu____4495 =
                                 let uu____4505 =
                                   FStar_List.map2
                                     (fun uu____4525  ->
                                        fun uu____4526  ->
                                          match (uu____4525, uu____4526) with
                                          | ((bv,uu____4543),(arg,q)) ->
                                              let uu____4550 =
                                                let uu____4551 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4551.FStar_Syntax_Syntax.n in
                                              (match uu____4550 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4561 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4574 ->
                                                   let uu____4575 =
                                                     check_n env arg in
                                                   (match uu____4575 with
                                                    | (uu____4586,s_arg,u_arg)
                                                        ->
                                                        let uu____4589 =
                                                          let uu____4593 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4593
                                                          then
                                                            let uu____4597 =
                                                              let uu____4600
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4600, q) in
                                                            [uu____4597;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4589))))
                                     binders2 args in
                                 FStar_List.split uu____4505 in
                               (match uu____4495 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4647 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4653 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4647, uu____4653)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,_)
        |FStar_Syntax_Syntax.Tm_meta (e1,_)|FStar_Syntax_Syntax.Tm_ascribed
         (e1,_,_) -> infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4731 = let uu____4732 = env.tc_const c in N uu____4732 in
          (uu____4731, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4733 ->
          let uu____4741 =
            let uu____4742 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4742 in
          failwith uu____4741
      | FStar_Syntax_Syntax.Tm_type uu____4746 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4750 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4761 ->
          let uu____4766 =
            let uu____4767 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4767 in
          failwith uu____4766
      | FStar_Syntax_Syntax.Tm_uvar uu____4771 ->
          let uu____4780 =
            let uu____4781 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4781 in
          failwith uu____4780
      | FStar_Syntax_Syntax.Tm_delayed uu____4785 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4809 =
            let uu____4810 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4810 in
          failwith uu____4809
and mk_match:
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t*
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option*
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
          let uu____4848 = check_n env e0 in
          match uu____4848 with
          | (uu____4855,s_e0,u_e0) ->
              let uu____4858 =
                let uu____4876 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4909 = FStar_Syntax_Subst.open_branch b in
                       match uu____4909 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___118_4941 = env in
                             let uu____4942 =
                               let uu____4943 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4943 in
                             {
                               env = uu____4942;
                               subst = (uu___118_4941.subst);
                               tc_const = (uu___118_4941.tc_const)
                             } in
                           let uu____4945 = f env1 body in
                           (match uu____4945 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4994 ->
                           Prims.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4876 in
              (match uu____4858 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5059 = FStar_List.hd nms in
                     match uu____5059 with | M t1|N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___102_5062  ->
                          match uu___102_5062 with
                          | M uu____5063 -> true
                          | uu____5064 -> false) nms in
                   let uu____5065 =
                     let uu____5088 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5140  ->
                              match uu____5140 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false )|(M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5236 =
                                         check env original_body (M t2) in
                                       (match uu____5236 with
                                        | (uu____5259,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5288,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5088 in
                   (match uu____5065 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5407  ->
                                 match uu____5407 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5448 =
                                         let uu____5449 =
                                           let uu____5459 =
                                             let uu____5463 =
                                               let uu____5466 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5467 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5466, uu____5467) in
                                             [uu____5463] in
                                           (s_body, uu____5459) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5449 in
                                       mk1 uu____5448 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5489 =
                              let uu____5490 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5490] in
                            let uu____5491 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5493 =
                              let uu____5500 =
                                let uu____5506 =
                                  let uu____5507 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5507 in
                                FStar_Util.Inl uu____5506 in
                              Some uu____5500 in
                            FStar_Syntax_Util.abs uu____5489 uu____5491
                              uu____5493 in
                          let t1_star =
                            let uu____5521 =
                              let uu____5525 =
                                let uu____5526 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5526 in
                              [uu____5525] in
                            let uu____5527 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5521 uu____5527 in
                          let uu____5530 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5560 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5530, uu____5560)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5574 =
                             let uu____5577 =
                               let uu____5578 =
                                 let uu____5596 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5596,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5578 in
                             mk1 uu____5577 in
                           let uu____5623 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5574, uu____5623))))
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
              let uu____5666 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5666] in
            let uu____5667 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5667 with
            | (x_binders1,e21) ->
                let uu____5675 = infer env e1 in
                (match uu____5675 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5686 = is_C t1 in
                       if uu____5686
                       then
                         let uu___119_5687 = binding in
                         let uu____5688 =
                           let uu____5691 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5691 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_5687.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_5687.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5688;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_5687.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_5687.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_5694 = env in
                       let uu____5695 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_5696 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_5696.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_5696.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5695;
                         subst = (uu___120_5694.subst);
                         tc_const = (uu___120_5694.tc_const)
                       } in
                     let uu____5697 = proceed env1 e21 in
                     (match uu____5697 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_5708 = binding in
                            let uu____5709 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_5708.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_5708.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5709;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_5708.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_5708.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5712 =
                            let uu____5715 =
                              let uu____5716 =
                                let uu____5724 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_5729 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_5729.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_5729.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_5729.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_5729.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5724) in
                              FStar_Syntax_Syntax.Tm_let uu____5716 in
                            mk1 uu____5715 in
                          let uu____5730 =
                            let uu____5733 =
                              let uu____5734 =
                                let uu____5742 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_5747 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_5747.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_5747.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_5747.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_5747.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5742) in
                              FStar_Syntax_Syntax.Tm_let uu____5734 in
                            mk1 uu____5733 in
                          (nm_rec, uu____5712, uu____5730))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_5756 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_5756.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_5756.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_5756.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_5758 = env in
                       let uu____5759 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_5760 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_5760.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_5760.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5759;
                         subst = (uu___126_5758.subst);
                         tc_const = (uu___126_5758.tc_const)
                       } in
                     let uu____5761 = ensure_m env1 e21 in
                     (match uu____5761 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5778 =
                              let uu____5779 =
                                let uu____5789 =
                                  let uu____5793 =
                                    let uu____5796 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5797 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5796, uu____5797) in
                                  [uu____5793] in
                                (s_e2, uu____5789) in
                              FStar_Syntax_Syntax.Tm_app uu____5779 in
                            mk1 uu____5778 in
                          let s_e22 =
                            let uu____5806 =
                              let uu____5813 =
                                let uu____5819 =
                                  let uu____5820 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5820 in
                                FStar_Util.Inl uu____5819 in
                              Some uu____5813 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____5806 in
                          let body =
                            let uu____5834 =
                              let uu____5835 =
                                let uu____5845 =
                                  let uu____5849 =
                                    let uu____5852 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5852) in
                                  [uu____5849] in
                                (s_e1, uu____5845) in
                              FStar_Syntax_Syntax.Tm_app uu____5835 in
                            mk1 uu____5834 in
                          let uu____5860 =
                            let uu____5861 =
                              let uu____5862 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5862] in
                            let uu____5863 =
                              let uu____5870 =
                                let uu____5876 =
                                  let uu____5877 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5877 in
                                FStar_Util.Inl uu____5876 in
                              Some uu____5870 in
                            FStar_Syntax_Util.abs uu____5861 body uu____5863 in
                          let uu____5888 =
                            let uu____5891 =
                              let uu____5892 =
                                let uu____5900 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_5905 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_5905.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_5905.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_5905.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_5905.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5900) in
                              FStar_Syntax_Syntax.Tm_let uu____5892 in
                            mk1 uu____5891 in
                          ((M t2), uu____5860, uu____5888)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5914 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____5914 in
      let uu____5919 = check env e mn in
      match uu____5919 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5929 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5942 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____5942 in
      let uu____5947 = check env e mn in
      match uu____5947 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5957 -> failwith "[check_m]: impossible"
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
        (let uu____5979 =
           let uu____5980 = is_C c in Prims.op_Negation uu____5980 in
         if uu____5979 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____5992 =
           let uu____5993 = FStar_Syntax_Subst.compress c in
           uu____5993.FStar_Syntax_Syntax.n in
         match uu____5992 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6012 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6012 with
              | (wp_head,wp_args) ->
                  ((let uu____6039 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6052 =
                           let uu____6053 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6053 in
                         Prims.op_Negation uu____6052) in
                    if uu____6039 then failwith "mismatch" else ());
                   (let uu____6062 =
                      let uu____6063 =
                        let uu____6073 =
                          FStar_List.map2
                            (fun uu____6083  ->
                               fun uu____6084  ->
                                 match (uu____6083, uu____6084) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6107 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6107
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6110 = print_implicit q in
                                         let uu____6111 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6110 uu____6111)
                                      else ();
                                      (let uu____6113 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6113, q)))) args wp_args in
                        (head1, uu____6073) in
                      FStar_Syntax_Syntax.Tm_app uu____6063 in
                    mk1 uu____6062)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6135 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6135 with
              | (binders_orig,comp1) ->
                  let uu____6140 =
                    let uu____6148 =
                      FStar_List.map
                        (fun uu____6162  ->
                           match uu____6162 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6175 = is_C h in
                               if uu____6175
                               then
                                 let w' =
                                   let uu____6182 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6182 in
                                 let uu____6183 =
                                   let uu____6187 =
                                     let uu____6191 =
                                       let uu____6194 =
                                         let uu____6195 =
                                           let uu____6196 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6196 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6195 in
                                       (uu____6194, q) in
                                     [uu____6191] in
                                   (w', q) :: uu____6187 in
                                 (w', uu____6183)
                               else
                                 (let x =
                                    let uu____6208 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6208 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6148 in
                  (match uu____6140 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6238 =
                           let uu____6240 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6240 in
                         FStar_Syntax_Subst.subst_comp uu____6238 comp1 in
                       let app =
                         let uu____6244 =
                           let uu____6245 =
                             let uu____6255 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6262 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6263 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6262, uu____6263)) bvs in
                             (wp, uu____6255) in
                           FStar_Syntax_Syntax.Tm_app uu____6245 in
                         mk1 uu____6244 in
                       let comp3 =
                         let uu____6268 = type_of_comp comp2 in
                         let uu____6269 = is_monadic_comp comp2 in
                         trans_G env uu____6268 uu____6269 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6271,uu____6272) ->
             trans_F_ env e wp
         | uu____6301 -> failwith "impossible trans_F_")
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
            let uu____6316 =
              let uu____6317 = star_type' env h in
              let uu____6320 =
                let uu____6326 =
                  let uu____6329 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6329) in
                [uu____6326] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6317;
                FStar_Syntax_Syntax.effect_args = uu____6320;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6316
          else
            (let uu____6335 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6335)
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
    fun t  -> let uu____6346 = n env.env t in star_type' env uu____6346
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6358 = n env.env t in check_n env uu____6358
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6368 = n env.env c in
        let uu____6369 = n env.env wp in trans_F_ env uu____6368 uu____6369