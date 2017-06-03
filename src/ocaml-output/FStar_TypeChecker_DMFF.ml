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
              let uu___101_64 = a in
              let uu____65 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___101_64.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___101_64.FStar_Syntax_Syntax.index);
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
                      let uu____953 =
                        let uu____954 =
                          let uu____964 = args_of_binders1 binders in
                          (c, uu____964) in
                        FStar_Syntax_Syntax.Tm_app uu____954 in
                      mk1 uu____953
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____972 =
                        let uu____973 =
                          let uu____977 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____978 =
                            let uu____980 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____980] in
                          uu____977 :: uu____978 in
                        let uu____981 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____973 uu____981 in
                      FStar_Syntax_Syntax.mk_Total uu____972 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____985 =
                      let uu____986 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____986 in
                    let uu____992 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____994 =
                        let uu____997 =
                          let uu____1003 =
                            let uu____1005 =
                              let uu____1008 =
                                let uu____1014 =
                                  let uu____1015 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1015 in
                                [uu____1014] in
                              FStar_Syntax_Util.mk_app l_ite uu____1008 in
                            [uu____1005] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1003 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____997 in
                      FStar_Syntax_Util.ascribe uu____994
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____985 uu____992
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1040 = mk_lid "wp_if_then_else" in
                    register env1 uu____1040 wp_if_then_else in
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
                      let uu____1051 =
                        let uu____1057 =
                          let uu____1059 =
                            let uu____1062 =
                              let uu____1068 =
                                let uu____1070 =
                                  let uu____1073 =
                                    let uu____1079 =
                                      let uu____1080 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1080 in
                                    [uu____1079] in
                                  FStar_Syntax_Util.mk_app l_and uu____1073 in
                                [uu____1070] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1068 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1062 in
                          let uu____1085 =
                            let uu____1089 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1089] in
                          uu____1059 :: uu____1085 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1057 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1051 in
                    let uu____1092 =
                      let uu____1093 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1093 in
                    FStar_Syntax_Util.abs uu____1092 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1100 = mk_lid "wp_assert" in
                    register env1 uu____1100 wp_assert in
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
                      let uu____1111 =
                        let uu____1117 =
                          let uu____1119 =
                            let uu____1122 =
                              let uu____1128 =
                                let uu____1130 =
                                  let uu____1133 =
                                    let uu____1139 =
                                      let uu____1140 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1140 in
                                    [uu____1139] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1133 in
                                [uu____1130] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1128 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1122 in
                          let uu____1145 =
                            let uu____1149 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1149] in
                          uu____1119 :: uu____1145 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1117 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1111 in
                    let uu____1152 =
                      let uu____1153 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1153 in
                    FStar_Syntax_Util.abs uu____1152 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1160 = mk_lid "wp_assume" in
                    register env1 uu____1160 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1169 =
                        let uu____1173 =
                          let uu____1174 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1174 in
                        [uu____1173] in
                      let uu____1175 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1169 uu____1175 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1182 =
                        let uu____1188 =
                          let uu____1190 =
                            let uu____1193 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1193 in
                          let uu____1199 =
                            let uu____1203 =
                              let uu____1206 =
                                let uu____1212 =
                                  let uu____1214 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1214] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1212 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1206 in
                            [uu____1203] in
                          uu____1190 :: uu____1199 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1188 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1182 in
                    let uu____1221 =
                      let uu____1222 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1222 in
                    FStar_Syntax_Util.abs uu____1221 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1229 = mk_lid "wp_close" in
                    register env1 uu____1229 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1240 =
                      let uu____1246 =
                        let uu____1247 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1247 in
                      FStar_Util.Inl uu____1246 in
                    Some uu____1240 in
                  let ret_gtot_type =
                    let uu____1267 =
                      let uu____1273 =
                        let uu____1274 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1274 in
                      FStar_Util.Inl uu____1273 in
                    Some uu____1267 in
                  let mk_forall1 x body =
                    let uu____1294 =
                      let uu____1297 =
                        let uu____1298 =
                          let uu____1308 =
                            let uu____1310 =
                              let uu____1311 =
                                let uu____1312 =
                                  let uu____1313 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1313] in
                                FStar_Syntax_Util.abs uu____1312 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1311 in
                            [uu____1310] in
                          (FStar_Syntax_Util.tforall, uu____1308) in
                        FStar_Syntax_Syntax.Tm_app uu____1298 in
                      FStar_Syntax_Syntax.mk uu____1297 in
                    uu____1294 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1327 =
                      let uu____1328 = FStar_Syntax_Subst.compress t in
                      uu____1328.FStar_Syntax_Syntax.n in
                    match uu____1327 with
                    | FStar_Syntax_Syntax.Tm_type uu____1331 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1346  ->
                              match uu____1346 with
                              | (b,uu____1350) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1351 -> true in
                  let rec is_monotonic t =
                    let uu____1356 =
                      let uu____1357 = FStar_Syntax_Subst.compress t in
                      uu____1357.FStar_Syntax_Syntax.n in
                    match uu____1356 with
                    | FStar_Syntax_Syntax.Tm_type uu____1360 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1375  ->
                              match uu____1375 with
                              | (b,uu____1379) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1380 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1432 =
                      let uu____1433 = FStar_Syntax_Subst.compress t1 in
                      uu____1433.FStar_Syntax_Syntax.n in
                    match uu____1432 with
                    | FStar_Syntax_Syntax.Tm_type uu____1436 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1439);
                                      FStar_Syntax_Syntax.tk = uu____1440;
                                      FStar_Syntax_Syntax.pos = uu____1441;
                                      FStar_Syntax_Syntax.vars = uu____1442;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1465 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1465
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1468 =
                              let uu____1471 =
                                let uu____1477 =
                                  let uu____1478 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1478 in
                                [uu____1477] in
                              FStar_Syntax_Util.mk_app x uu____1471 in
                            let uu____1479 =
                              let uu____1482 =
                                let uu____1488 =
                                  let uu____1489 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1489 in
                                [uu____1488] in
                              FStar_Syntax_Util.mk_app y uu____1482 in
                            mk_rel1 b uu____1468 uu____1479 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1496 =
                               let uu____1497 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1500 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1497 uu____1500 in
                             let uu____1503 =
                               let uu____1504 =
                                 let uu____1507 =
                                   let uu____1513 =
                                     let uu____1514 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1514 in
                                   [uu____1513] in
                                 FStar_Syntax_Util.mk_app x uu____1507 in
                               let uu____1515 =
                                 let uu____1518 =
                                   let uu____1524 =
                                     let uu____1525 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1525 in
                                   [uu____1524] in
                                 FStar_Syntax_Util.mk_app y uu____1518 in
                               mk_rel1 b uu____1504 uu____1515 in
                             FStar_Syntax_Util.mk_imp uu____1496 uu____1503 in
                           let uu____1526 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1526)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1529);
                                      FStar_Syntax_Syntax.tk = uu____1530;
                                      FStar_Syntax_Syntax.pos = uu____1531;
                                      FStar_Syntax_Syntax.vars = uu____1532;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1555 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1555
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1558 =
                              let uu____1561 =
                                let uu____1567 =
                                  let uu____1568 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1568 in
                                [uu____1567] in
                              FStar_Syntax_Util.mk_app x uu____1561 in
                            let uu____1569 =
                              let uu____1572 =
                                let uu____1578 =
                                  let uu____1579 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1579 in
                                [uu____1578] in
                              FStar_Syntax_Util.mk_app y uu____1572 in
                            mk_rel1 b uu____1558 uu____1569 in
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
                      let uu____1685 =
                        let uu____1686 = FStar_Syntax_Subst.compress t1 in
                        uu____1686.FStar_Syntax_Syntax.n in
                      match uu____1685 with
                      | FStar_Syntax_Syntax.Tm_type uu____1691 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1708 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1708
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1723 =
                                let uu____1724 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1724 i in
                              FStar_Syntax_Syntax.fvar uu____1723
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1748 =
                            let uu____1756 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1765  ->
                                     match uu____1765 with
                                     | (t2,q) ->
                                         let uu____1772 = project i x in
                                         let uu____1773 = project i y in
                                         mk_stronger t2 uu____1772 uu____1773)
                                args in
                            match uu____1756 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1748 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1820);
                                      FStar_Syntax_Syntax.tk = uu____1821;
                                      FStar_Syntax_Syntax.pos = uu____1822;
                                      FStar_Syntax_Syntax.vars = uu____1823;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1845  ->
                                   match uu____1845 with
                                   | (bv,q) ->
                                       let uu____1850 =
                                         let uu____1851 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1851 in
                                       FStar_Syntax_Syntax.gen_bv uu____1850
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1855 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1855) bvs in
                          let body =
                            let uu____1859 = FStar_Syntax_Util.mk_app x args in
                            let uu____1860 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1859 uu____1860 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1865);
                                      FStar_Syntax_Syntax.tk = uu____1866;
                                      FStar_Syntax_Syntax.pos = uu____1867;
                                      FStar_Syntax_Syntax.vars = uu____1868;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1890  ->
                                   match uu____1890 with
                                   | (bv,q) ->
                                       let uu____1895 =
                                         let uu____1896 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1896 in
                                       FStar_Syntax_Syntax.gen_bv uu____1895
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1900 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1900) bvs in
                          let body =
                            let uu____1904 = FStar_Syntax_Util.mk_app x args in
                            let uu____1905 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1904 uu____1905 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1908 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1914 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1915 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1916 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1914 uu____1915 uu____1916 in
                    let uu____1917 =
                      let uu____1918 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1918 in
                    FStar_Syntax_Util.abs uu____1917 body ret_tot_type in
                  let stronger1 =
                    let uu____1933 = mk_lid "stronger" in
                    register env1 uu____1933 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1939 = FStar_Util.prefix gamma in
                    match uu____1939 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1965 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1965 in
                          let uu____1968 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1968 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1976 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1976 in
                              let guard_free1 =
                                let uu____1983 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1983 in
                              let pat =
                                let uu____1987 =
                                  let uu____1993 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1993] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1987 in
                              let pattern_guarded_body =
                                let uu____1997 =
                                  let uu____1998 =
                                    let uu____2003 =
                                      let uu____2004 =
                                        let uu____2011 =
                                          let uu____2013 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____2013] in
                                        [uu____2011] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2004 in
                                    (body, uu____2003) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1998 in
                                mk1 uu____1997 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2016 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____2019 =
                            let uu____2020 =
                              let uu____2021 =
                                let uu____2022 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____2025 =
                                  let uu____2031 = args_of_binders1 wp_args in
                                  let uu____2033 =
                                    let uu____2035 =
                                      let uu____2036 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2036 in
                                    [uu____2035] in
                                  FStar_List.append uu____2031 uu____2033 in
                                FStar_Syntax_Util.mk_app uu____2022
                                  uu____2025 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2021 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2020 in
                          FStar_Syntax_Util.abs gamma uu____2019
                            ret_gtot_type in
                        let uu____2037 =
                          let uu____2038 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2038 in
                        FStar_Syntax_Util.abs uu____2037 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2045 = mk_lid "wp_ite" in
                    register env1 uu____2045 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2051 = FStar_Util.prefix gamma in
                    match uu____2051 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2075 =
                            let uu____2076 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2079 =
                              let uu____2085 =
                                let uu____2086 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2086 in
                              [uu____2085] in
                            FStar_Syntax_Util.mk_app uu____2076 uu____2079 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2075 in
                        let uu____2087 =
                          let uu____2088 =
                            let uu____2092 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2092 gamma in
                          FStar_List.append binders uu____2088 in
                        FStar_Syntax_Util.abs uu____2087 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2101 = mk_lid "null_wp" in
                    register env1 uu____2101 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2110 =
                        let uu____2116 =
                          let uu____2118 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2119 =
                            let uu____2121 =
                              let uu____2124 =
                                let uu____2130 =
                                  let uu____2131 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2131 in
                                [uu____2130] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2124 in
                            let uu____2132 =
                              let uu____2136 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2136] in
                            uu____2121 :: uu____2132 in
                          uu____2118 :: uu____2119 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2116 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2110 in
                    let uu____2139 =
                      let uu____2140 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2140 in
                    FStar_Syntax_Util.abs uu____2139 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2147 = mk_lid "wp_trivial" in
                    register env1 uu____2147 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2152 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2152
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2157 =
                      let uu____2159 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2159 in
                    let uu____2164 =
                      let uu___103_2165 = ed in
                      let uu____2166 =
                        let uu____2167 = c wp_if_then_else2 in
                        ([], uu____2167) in
                      let uu____2169 =
                        let uu____2170 = c wp_ite2 in ([], uu____2170) in
                      let uu____2172 =
                        let uu____2173 = c stronger2 in ([], uu____2173) in
                      let uu____2175 =
                        let uu____2176 = c wp_close2 in ([], uu____2176) in
                      let uu____2178 =
                        let uu____2179 = c wp_assert2 in ([], uu____2179) in
                      let uu____2181 =
                        let uu____2182 = c wp_assume2 in ([], uu____2182) in
                      let uu____2184 =
                        let uu____2185 = c null_wp2 in ([], uu____2185) in
                      let uu____2187 =
                        let uu____2188 = c wp_trivial2 in ([], uu____2188) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_2165.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_2165.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_2165.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_2165.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_2165.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_2165.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_2165.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2166;
                        FStar_Syntax_Syntax.ite_wp = uu____2169;
                        FStar_Syntax_Syntax.stronger = uu____2172;
                        FStar_Syntax_Syntax.close_wp = uu____2175;
                        FStar_Syntax_Syntax.assert_p = uu____2178;
                        FStar_Syntax_Syntax.assume_p = uu____2181;
                        FStar_Syntax_Syntax.null_wp = uu____2184;
                        FStar_Syntax_Syntax.trivial = uu____2187;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_2165.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_2165.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_2165.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_2165.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2157, uu____2164)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_2200 = dmff_env in
      {
        env = env';
        subst = (uu___104_2200.subst);
        tc_const = (uu___104_2200.tc_const)
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
            | uu____2653 ->
                ((let uu____2655 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2655);
                 false) in
          let rec is_valid_application head2 =
            let uu____2660 =
              let uu____2661 = FStar_Syntax_Subst.compress head2 in
              uu____2661.FStar_Syntax_Syntax.n in
            match uu____2660 with
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
                  (let uu____2665 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2665)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2680 -> true
                 | uu____2690 ->
                     ((let uu____2692 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2692);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2693 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2694 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2696) ->
                is_valid_application t2
            | uu____2701 -> false in
          let uu____2702 = is_valid_application head1 in
          if uu____2702
          then
            let uu____2703 =
              let uu____2704 =
                let uu____2714 =
                  FStar_List.map
                    (fun uu____2724  ->
                       match uu____2724 with
                       | (t2,qual) ->
                           let uu____2737 = star_type' env t2 in
                           (uu____2737, qual)) args in
                (head1, uu____2714) in
              FStar_Syntax_Syntax.Tm_app uu____2704 in
            mk1 uu____2703
          else
            (let uu____2744 =
               let uu____2745 =
                 let uu____2746 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2746 in
               FStar_Errors.Err uu____2745 in
             raise uu____2744)
      | FStar_Syntax_Syntax.Tm_bvar uu____2747 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2748 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2749 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2750 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2776 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2776 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___108_2782 = env in
                 let uu____2783 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2783;
                   subst = (uu___108_2782.subst);
                   tc_const = (uu___108_2782.tc_const)
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
               ((let uu___109_2800 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_2800.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_2800.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2807 =
            let uu____2808 =
              let uu____2813 = star_type' env t2 in (uu____2813, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2808 in
          mk1 uu____2807
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2851 =
            let uu____2852 =
              let uu____2870 = star_type' env e in
              let uu____2871 =
                let uu____2881 =
                  let uu____2886 = star_type' env t2 in
                  FStar_Util.Inl uu____2886 in
                (uu____2881, None) in
              (uu____2870, uu____2871, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2852 in
          mk1 uu____2851
      | FStar_Syntax_Syntax.Tm_ascribed uu____2908 ->
          let uu____2926 =
            let uu____2927 =
              let uu____2928 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2928 in
            FStar_Errors.Err uu____2927 in
          raise uu____2926
      | FStar_Syntax_Syntax.Tm_refine uu____2929 ->
          let uu____2934 =
            let uu____2935 =
              let uu____2936 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2936 in
            FStar_Errors.Err uu____2935 in
          raise uu____2934
      | FStar_Syntax_Syntax.Tm_uinst uu____2937 ->
          let uu____2942 =
            let uu____2943 =
              let uu____2944 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2944 in
            FStar_Errors.Err uu____2943 in
          raise uu____2942
      | FStar_Syntax_Syntax.Tm_constant uu____2945 ->
          let uu____2946 =
            let uu____2947 =
              let uu____2948 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2948 in
            FStar_Errors.Err uu____2947 in
          raise uu____2946
      | FStar_Syntax_Syntax.Tm_match uu____2949 ->
          let uu____2965 =
            let uu____2966 =
              let uu____2967 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2967 in
            FStar_Errors.Err uu____2966 in
          raise uu____2965
      | FStar_Syntax_Syntax.Tm_let uu____2968 ->
          let uu____2976 =
            let uu____2977 =
              let uu____2978 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2978 in
            FStar_Errors.Err uu____2977 in
          raise uu____2976
      | FStar_Syntax_Syntax.Tm_uvar uu____2979 ->
          let uu____2988 =
            let uu____2989 =
              let uu____2990 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2990 in
            FStar_Errors.Err uu____2989 in
          raise uu____2988
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2991 =
            let uu____2992 =
              let uu____2993 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2993 in
            FStar_Errors.Err uu____2992 in
          raise uu____2991
      | FStar_Syntax_Syntax.Tm_delayed uu____2994 -> failwith "impossible"
let is_monadic uu___93_3027 =
  match uu___93_3027 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3039;
        FStar_Syntax_Syntax.res_typ = uu____3040;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3042;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3059  ->
              match uu___92_3059 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3060 -> false))
  | Some (FStar_Util.Inr (uu____3061,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3074  ->
              match uu___92_3074 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3075 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3079 =
      let uu____3080 = FStar_Syntax_Subst.compress t in
      uu____3080.FStar_Syntax_Syntax.n in
    match uu____3079 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3100 =
            let uu____3101 = FStar_List.hd args in fst uu____3101 in
          is_C uu____3100 in
        if r
        then
          ((let uu____3113 =
              let uu____3114 =
                FStar_List.for_all
                  (fun uu____3117  ->
                     match uu____3117 with | (h,uu____3121) -> is_C h) args in
              Prims.op_Negation uu____3114 in
            if uu____3113 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3125 =
              let uu____3126 =
                FStar_List.for_all
                  (fun uu____3129  ->
                     match uu____3129 with
                     | (h,uu____3133) ->
                         let uu____3134 = is_C h in
                         Prims.op_Negation uu____3134) args in
              Prims.op_Negation uu____3126 in
            if uu____3125 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3148 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3148 with
         | M t1 ->
             ((let uu____3151 = is_C t1 in
               if uu____3151 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3155) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3161) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3167,uu____3168) -> is_C t1
    | uu____3197 -> false
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
          let uu____3224 =
            let uu____3225 =
              let uu____3235 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3236 =
                let uu____3240 =
                  let uu____3243 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3243) in
                [uu____3240] in
              (uu____3235, uu____3236) in
            FStar_Syntax_Syntax.Tm_app uu____3225 in
          mk1 uu____3224 in
        let uu____3251 =
          let uu____3252 = FStar_Syntax_Syntax.mk_binder p in [uu____3252] in
        let uu____3253 =
          let uu____3260 =
            let uu____3266 =
              let uu____3267 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3267 in
            FStar_Util.Inl uu____3266 in
          Some uu____3260 in
        FStar_Syntax_Util.abs uu____3251 body uu____3253
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___94_3280  ->
    match uu___94_3280 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3281 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
        let return_if uu____3425 =
          match uu____3425 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3446 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3447 =
                       let uu____3448 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3448 in
                     Prims.op_Negation uu____3447) in
                if uu____3446
                then
                  let uu____3449 =
                    let uu____3450 =
                      let uu____3451 = FStar_Syntax_Print.term_to_string e in
                      let uu____3452 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3453 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3451 uu____3452 uu____3453 in
                    FStar_Errors.Err uu____3450 in
                  raise uu____3449
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3467 = mk_return env t1 s_e in
                     ((M t1), uu____3467, u_e)))
               | (M t1,N t2) ->
                   let uu____3470 =
                     let uu____3471 =
                       let uu____3472 = FStar_Syntax_Print.term_to_string e in
                       let uu____3473 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3474 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3472 uu____3473 uu____3474 in
                     FStar_Errors.Err uu____3471 in
                   raise uu____3470) in
        let ensure_m env1 e2 =
          let strip_m uu___95_3500 =
            match uu___95_3500 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3510 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3521 =
                let uu____3522 =
                  let uu____3525 =
                    let uu____3526 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3526 in
                  (uu____3525, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3522 in
              raise uu____3521
          | M uu____3530 ->
              let uu____3531 = check env1 e2 context_nm in strip_m uu____3531 in
        let uu____3535 =
          let uu____3536 = FStar_Syntax_Subst.compress e in
          uu____3536.FStar_Syntax_Syntax.n in
        match uu____3535 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3542 ->
            let uu____3543 = infer env e in return_if uu____3543
        | FStar_Syntax_Syntax.Tm_name uu____3547 ->
            let uu____3548 = infer env e in return_if uu____3548
        | FStar_Syntax_Syntax.Tm_fvar uu____3552 ->
            let uu____3553 = infer env e in return_if uu____3553
        | FStar_Syntax_Syntax.Tm_abs uu____3557 ->
            let uu____3572 = infer env e in return_if uu____3572
        | FStar_Syntax_Syntax.Tm_constant uu____3576 ->
            let uu____3577 = infer env e in return_if uu____3577
        | FStar_Syntax_Syntax.Tm_app uu____3581 ->
            let uu____3591 = infer env e in return_if uu____3591
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3638) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3644) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3650,uu____3651) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3680 ->
            let uu____3688 =
              let uu____3689 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3689 in
            failwith uu____3688
        | FStar_Syntax_Syntax.Tm_type uu____3693 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3697 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3708 ->
            let uu____3713 =
              let uu____3714 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3714 in
            failwith uu____3713
        | FStar_Syntax_Syntax.Tm_uvar uu____3718 ->
            let uu____3727 =
              let uu____3728 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3728 in
            failwith uu____3727
        | FStar_Syntax_Syntax.Tm_delayed uu____3732 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3756 =
              let uu____3757 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3757 in
            failwith uu____3756
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
      let uu____3779 =
        let uu____3780 = FStar_Syntax_Subst.compress e in
        uu____3780.FStar_Syntax_Syntax.n in
      match uu____3779 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___110_3820 = env in
            let uu____3821 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3821;
              subst = (uu___110_3820.subst);
              tc_const = (uu___110_3820.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3830  ->
                 match uu____3830 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___111_3838 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___111_3838.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___111_3838.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3839 =
            FStar_List.fold_left
              (fun uu____3848  ->
                 fun uu____3849  ->
                   match (uu____3848, uu____3849) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3877 = is_C c in
                       if uu____3877
                       then
                         let xw =
                           let uu____3882 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3882 in
                         let x =
                           let uu___112_3884 = bv in
                           let uu____3885 =
                             let uu____3888 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3888 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___112_3884.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___112_3884.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3885
                           } in
                         let env3 =
                           let uu___113_3890 = env2 in
                           let uu____3891 =
                             let uu____3893 =
                               let uu____3894 =
                                 let uu____3899 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3899) in
                               FStar_Syntax_Syntax.NT uu____3894 in
                             uu____3893 :: (env2.subst) in
                           {
                             env = (uu___113_3890.env);
                             subst = uu____3891;
                             tc_const = (uu___113_3890.tc_const)
                           } in
                         let uu____3900 =
                           let uu____3902 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3903 =
                             let uu____3905 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3905 :: acc in
                           uu____3902 :: uu____3903 in
                         (env3, uu____3900)
                       else
                         (let x =
                            let uu___114_3909 = bv in
                            let uu____3910 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_3909.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_3909.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3910
                            } in
                          let uu____3913 =
                            let uu____3915 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3915 :: acc in
                          (env2, uu____3913))) (env1, []) binders1 in
          (match uu____3839 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3927 =
                 let check_what =
                   let uu____3939 = is_monadic what in
                   if uu____3939 then check_m else check_n in
                 let uu____3948 = check_what env2 body1 in
                 match uu____3948 with
                 | (t,s_body,u_body) ->
                     let uu____3958 =
                       let uu____3959 =
                         let uu____3960 = is_monadic what in
                         if uu____3960 then M t else N t in
                       comp_of_nm uu____3959 in
                     (uu____3958, s_body, u_body) in
               (match uu____3927 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____4003 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___96_4005  ->
                                    match uu___96_4005 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____4006 -> false)) in
                          if uu____4003
                          then
                            let double_starred_comp =
                              let uu____4014 =
                                let uu____4015 =
                                  let uu____4016 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____4016 in
                                FStar_All.pipe_left double_star uu____4015 in
                              FStar_Syntax_Syntax.mk_Total uu____4014 in
                            let flags =
                              FStar_List.filter
                                (fun uu___97_4021  ->
                                   match uu___97_4021 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____4022 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____4023 =
                              let uu____4029 =
                                let uu____4030 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____4030 in
                              FStar_Util.Inl uu____4029 in
                            Some uu____4023
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___115_4050 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___115_4050.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___115_4050.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___115_4050.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4051  ->
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
                          let uu____4068 =
                            let uu____4074 =
                              let uu____4078 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___98_4080  ->
                                        match uu___98_4080 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4081 -> false)) in
                              if uu____4078
                              then
                                let uu____4085 =
                                  FStar_List.filter
                                    (fun uu___99_4087  ->
                                       match uu___99_4087 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4088 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4085)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4074 in
                          Some uu____4068 in
                    let uu____4100 =
                      let comp1 =
                        let uu____4112 = is_monadic what in
                        let uu____4113 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4112 uu____4113 in
                      let uu____4114 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4114,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4100 with
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
                FStar_Syntax_Syntax.ty = uu____4192;
                FStar_Syntax_Syntax.p = uu____4193;_};
            FStar_Syntax_Syntax.fv_delta = uu____4194;
            FStar_Syntax_Syntax.fv_qual = uu____4195;_}
          ->
          let uu____4201 =
            let uu____4204 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4204 in
          (match uu____4201 with
           | (uu____4220,t) ->
               let uu____4222 = let uu____4223 = normalize1 t in N uu____4223 in
               (uu____4222, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4240 = check_n env head1 in
          (match uu____4240 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4254 =
                   let uu____4255 = FStar_Syntax_Subst.compress t in
                   uu____4255.FStar_Syntax_Syntax.n in
                 match uu____4254 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4258 -> true
                 | uu____4266 -> false in
               let rec flatten1 t =
                 let uu____4278 =
                   let uu____4279 = FStar_Syntax_Subst.compress t in
                   uu____4279.FStar_Syntax_Syntax.n in
                 match uu____4278 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4291);
                                FStar_Syntax_Syntax.tk = uu____4292;
                                FStar_Syntax_Syntax.pos = uu____4293;
                                FStar_Syntax_Syntax.vars = uu____4294;_})
                     when is_arrow t1 ->
                     let uu____4311 = flatten1 t1 in
                     (match uu____4311 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4363,uu____4364)
                     -> flatten1 e1
                 | uu____4393 ->
                     let uu____4394 =
                       let uu____4395 =
                         let uu____4396 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4396 in
                       FStar_Errors.Err uu____4395 in
                     raise uu____4394 in
               let uu____4404 = flatten1 t_head in
               (match uu____4404 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4456 =
                          let uu____4457 =
                            let uu____4458 = FStar_Util.string_of_int n1 in
                            let uu____4465 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4476 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4458 uu____4465 uu____4476 in
                          FStar_Errors.Err uu____4457 in
                        raise uu____4456)
                     else ();
                     (let uu____4484 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4484 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4511 args1 =
                            match uu____4511 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4554 =
                                       let uu____4555 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4555.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4554
                                 | (binders3,[]) ->
                                     let uu____4574 =
                                       let uu____4575 =
                                         let uu____4578 =
                                           let uu____4579 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4579 in
                                         FStar_Syntax_Subst.compress
                                           uu____4578 in
                                       uu____4575.FStar_Syntax_Syntax.n in
                                     (match uu____4574 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4595 =
                                            let uu____4596 =
                                              let uu____4597 =
                                                let uu____4605 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4605) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4597 in
                                            mk1 uu____4596 in
                                          N uu____4595
                                      | uu____4609 -> failwith "wat?")
                                 | ([],uu____4610::uu____4611) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4636)::binders3,(arg,uu____4639)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4673 = FStar_List.splitAt n' binders1 in
                          (match uu____4673 with
                           | (binders2,uu____4692) ->
                               let uu____4705 =
                                 let uu____4715 =
                                   FStar_List.map2
                                     (fun uu____4735  ->
                                        fun uu____4736  ->
                                          match (uu____4735, uu____4736) with
                                          | ((bv,uu____4753),(arg,q)) ->
                                              let uu____4760 =
                                                let uu____4761 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4761.FStar_Syntax_Syntax.n in
                                              (match uu____4760 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4771 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4784 ->
                                                   let uu____4785 =
                                                     check_n env arg in
                                                   (match uu____4785 with
                                                    | (uu____4796,s_arg,u_arg)
                                                        ->
                                                        let uu____4799 =
                                                          let uu____4803 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4803
                                                          then
                                                            let uu____4807 =
                                                              let uu____4810
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4810, q) in
                                                            [uu____4807;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4799))))
                                     binders2 args in
                                 FStar_List.split uu____4715 in
                               (match uu____4705 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4857 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4863 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4857, uu____4863)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4912) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4918) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4924,uu____4925) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4955 = let uu____4956 = env.tc_const c in N uu____4956 in
          (uu____4955, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4957 ->
          let uu____4965 =
            let uu____4966 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4966 in
          failwith uu____4965
      | FStar_Syntax_Syntax.Tm_type uu____4970 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4974 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4985 ->
          let uu____4990 =
            let uu____4991 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4991 in
          failwith uu____4990
      | FStar_Syntax_Syntax.Tm_uvar uu____4995 ->
          let uu____5004 =
            let uu____5005 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____5005 in
          failwith uu____5004
      | FStar_Syntax_Syntax.Tm_delayed uu____5009 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5033 =
            let uu____5034 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____5034 in
          failwith uu____5033
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
          let uu____5072 = check_n env e0 in
          match uu____5072 with
          | (uu____5079,s_e0,u_e0) ->
              let uu____5082 =
                let uu____5100 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5133 = FStar_Syntax_Subst.open_branch b in
                       match uu____5133 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___116_5165 = env in
                             let uu____5166 =
                               let uu____5167 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5167 in
                             {
                               env = uu____5166;
                               subst = (uu___116_5165.subst);
                               tc_const = (uu___116_5165.tc_const)
                             } in
                           let uu____5169 = f env1 body in
                           (match uu____5169 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5218 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5100 in
              (match uu____5082 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5283 = FStar_List.hd nms in
                     match uu____5283 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_5287  ->
                          match uu___100_5287 with
                          | M uu____5288 -> true
                          | uu____5289 -> false) nms in
                   let uu____5290 =
                     let uu____5313 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5365  ->
                              match uu____5365 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5488 =
                                         check env original_body (M t2) in
                                       (match uu____5488 with
                                        | (uu____5511,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5540,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5313 in
                   (match uu____5290 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5659  ->
                                 match uu____5659 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5700 =
                                         let uu____5701 =
                                           let uu____5711 =
                                             let uu____5715 =
                                               let uu____5718 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5719 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5718, uu____5719) in
                                             [uu____5715] in
                                           (s_body, uu____5711) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5701 in
                                       mk1 uu____5700 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5741 =
                              let uu____5742 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5742] in
                            let uu____5743 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5745 =
                              let uu____5752 =
                                let uu____5758 =
                                  let uu____5759 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5759 in
                                FStar_Util.Inl uu____5758 in
                              Some uu____5752 in
                            FStar_Syntax_Util.abs uu____5741 uu____5743
                              uu____5745 in
                          let t1_star =
                            let uu____5773 =
                              let uu____5777 =
                                let uu____5778 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5778 in
                              [uu____5777] in
                            let uu____5779 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5773 uu____5779 in
                          let uu____5782 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5812 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5782, uu____5812)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5826 =
                             let uu____5829 =
                               let uu____5830 =
                                 let uu____5848 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5848,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5830 in
                             mk1 uu____5829 in
                           let uu____5875 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5826, uu____5875))))
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
              let uu____5918 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5918] in
            let uu____5919 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5919 with
            | (x_binders1,e21) ->
                let uu____5927 = infer env e1 in
                (match uu____5927 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5938 = is_C t1 in
                       if uu____5938
                       then
                         let uu___117_5939 = binding in
                         let uu____5940 =
                           let uu____5943 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5943 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___117_5939.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___117_5939.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5940;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___117_5939.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___117_5939.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___118_5946 = env in
                       let uu____5947 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5948 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5948.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5948.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5947;
                         subst = (uu___118_5946.subst);
                         tc_const = (uu___118_5946.tc_const)
                       } in
                     let uu____5949 = proceed env1 e21 in
                     (match uu____5949 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___120_5960 = binding in
                            let uu____5961 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_5960.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___120_5960.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5961;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_5960.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___120_5960.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5964 =
                            let uu____5967 =
                              let uu____5968 =
                                let uu____5976 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___121_5981 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5981.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5981.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5981.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5981.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5976) in
                              FStar_Syntax_Syntax.Tm_let uu____5968 in
                            mk1 uu____5967 in
                          let uu____5982 =
                            let uu____5985 =
                              let uu____5986 =
                                let uu____5994 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___122_5999 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_5999.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_5999.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_5999.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_5999.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5994) in
                              FStar_Syntax_Syntax.Tm_let uu____5986 in
                            mk1 uu____5985 in
                          (nm_rec, uu____5964, uu____5982))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___123_6008 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___123_6008.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___123_6008.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___123_6008.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___124_6010 = env in
                       let uu____6011 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_6012 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_6012.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_6012.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____6011;
                         subst = (uu___124_6010.subst);
                         tc_const = (uu___124_6010.tc_const)
                       } in
                     let uu____6013 = ensure_m env1 e21 in
                     (match uu____6013 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____6030 =
                              let uu____6031 =
                                let uu____6041 =
                                  let uu____6045 =
                                    let uu____6048 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6049 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6048, uu____6049) in
                                  [uu____6045] in
                                (s_e2, uu____6041) in
                              FStar_Syntax_Syntax.Tm_app uu____6031 in
                            mk1 uu____6030 in
                          let s_e22 =
                            let uu____6058 =
                              let uu____6065 =
                                let uu____6071 =
                                  let uu____6072 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6072 in
                                FStar_Util.Inl uu____6071 in
                              Some uu____6065 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6058 in
                          let body =
                            let uu____6086 =
                              let uu____6087 =
                                let uu____6097 =
                                  let uu____6101 =
                                    let uu____6104 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6104) in
                                  [uu____6101] in
                                (s_e1, uu____6097) in
                              FStar_Syntax_Syntax.Tm_app uu____6087 in
                            mk1 uu____6086 in
                          let uu____6112 =
                            let uu____6113 =
                              let uu____6114 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6114] in
                            let uu____6115 =
                              let uu____6122 =
                                let uu____6128 =
                                  let uu____6129 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6129 in
                                FStar_Util.Inl uu____6128 in
                              Some uu____6122 in
                            FStar_Syntax_Util.abs uu____6113 body uu____6115 in
                          let uu____6140 =
                            let uu____6143 =
                              let uu____6144 =
                                let uu____6152 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___126_6157 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_6157.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_6157.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_6157.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_6157.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6152) in
                              FStar_Syntax_Syntax.Tm_let uu____6144 in
                            mk1 uu____6143 in
                          ((M t2), uu____6112, uu____6140)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6166 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6166 in
      let uu____6171 = check env e mn in
      match uu____6171 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6181 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6194 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6194 in
      let uu____6199 = check env e mn in
      match uu____6199 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6209 -> failwith "[check_m]: impossible"
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
        (let uu____6231 =
           let uu____6232 = is_C c in Prims.op_Negation uu____6232 in
         if uu____6231 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6244 =
           let uu____6245 = FStar_Syntax_Subst.compress c in
           uu____6245.FStar_Syntax_Syntax.n in
         match uu____6244 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6264 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6264 with
              | (wp_head,wp_args) ->
                  ((let uu____6291 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6308 =
                           let uu____6309 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6309 in
                         Prims.op_Negation uu____6308) in
                    if uu____6291 then failwith "mismatch" else ());
                   (let uu____6321 =
                      let uu____6322 =
                        let uu____6332 =
                          FStar_List.map2
                            (fun uu____6342  ->
                               fun uu____6343  ->
                                 match (uu____6342, uu____6343) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6366 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6366
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6369 = print_implicit q in
                                         let uu____6370 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6369 uu____6370)
                                      else ();
                                      (let uu____6372 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6372, q)))) args wp_args in
                        (head1, uu____6332) in
                      FStar_Syntax_Syntax.Tm_app uu____6322 in
                    mk1 uu____6321)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6394 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6394 with
              | (binders_orig,comp1) ->
                  let uu____6399 =
                    let uu____6407 =
                      FStar_List.map
                        (fun uu____6421  ->
                           match uu____6421 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6434 = is_C h in
                               if uu____6434
                               then
                                 let w' =
                                   let uu____6441 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6441 in
                                 let uu____6442 =
                                   let uu____6446 =
                                     let uu____6450 =
                                       let uu____6453 =
                                         let uu____6454 =
                                           let uu____6455 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6455 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6454 in
                                       (uu____6453, q) in
                                     [uu____6450] in
                                   (w', q) :: uu____6446 in
                                 (w', uu____6442)
                               else
                                 (let x =
                                    let uu____6467 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6467 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6407 in
                  (match uu____6399 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6497 =
                           let uu____6499 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6499 in
                         FStar_Syntax_Subst.subst_comp uu____6497 comp1 in
                       let app =
                         let uu____6503 =
                           let uu____6504 =
                             let uu____6514 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6521 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6522 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6521, uu____6522)) bvs in
                             (wp, uu____6514) in
                           FStar_Syntax_Syntax.Tm_app uu____6504 in
                         mk1 uu____6503 in
                       let comp3 =
                         let uu____6527 = type_of_comp comp2 in
                         let uu____6528 = is_monadic_comp comp2 in
                         trans_G env uu____6527 uu____6528 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6530,uu____6531) ->
             trans_F_ env e wp
         | uu____6560 -> failwith "impossible trans_F_")
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
            let uu____6575 =
              let uu____6576 = star_type' env h in
              let uu____6579 =
                let uu____6585 =
                  let uu____6588 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6588) in
                [uu____6585] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6576;
                FStar_Syntax_Syntax.effect_args = uu____6579;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6575
          else
            (let uu____6594 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6594)
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
    fun t  -> let uu____6605 = n env.env t in star_type' env uu____6605
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6617 = n env.env t in check_n env uu____6617
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6627 = n env.env c in
        let uu____6628 = n env.env wp in trans_F_ env uu____6627 uu____6628