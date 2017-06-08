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
            (FStar_Syntax_Syntax.sigelts,FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2
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
                (FStar_Syntax_Syntax.mk x) FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
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
                     ((FStar_Pervasives_Native.fst t), uu____239)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____252 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____252) in
              let uu____253 =
                let uu____265 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
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
                    FStar_Syntax_Util.abs uu____288 body
                      FStar_Pervasives_Native.None in
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
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____430 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____430 in
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
                      FStar_Pervasives_Native.Some uu____438 in
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
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____485 =
                        let uu____486 =
                          let uu____487 =
                            let uu____491 =
                              let uu____492 =
                                let uu____493 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____493 in
                              FStar_Syntax_Syntax.mk_binder uu____492 in
                            [uu____491] in
                          let uu____494 =
                            let uu____497 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____497 in
                          FStar_Syntax_Util.arrow uu____487 uu____494 in
                        mk_gctx uu____486 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____485 in
                    let r =
                      let uu____499 =
                        let uu____500 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____500 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____499 in
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
                      FStar_Pervasives_Native.Some uu____508 in
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
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
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
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____593 =
                        let uu____594 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____594 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____593 in
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
                      FStar_Pervasives_Native.Some uu____602 in
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
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
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
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____698 =
                        let uu____699 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____699 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____698 in
                    let a2 =
                      let uu____701 =
                        let uu____702 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____702 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____701 in
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
                      FStar_Pervasives_Native.Some uu____710 in
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
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
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
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
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
                      FStar_Pervasives_Native.Some uu____830 in
                    let e1 =
                      let uu____861 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____861 in
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
                    FStar_Pervasives_Native.Some uu____915 in
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
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____982 =
                      let uu____983 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____983 in
                    let uu____989 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
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
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____982 uu____989
                      (FStar_Pervasives_Native.Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1037 = mk_lid "wp_if_then_else" in
                    register env1 uu____1037 wp_if_then_else in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1 in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None in
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
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None in
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
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1166 =
                        let uu____1170 =
                          let uu____1171 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1171 in
                        [uu____1170] in
                      let uu____1172 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1166 uu____1172 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
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
                    FStar_Pervasives_Native.Some uu____1237 in
                  let ret_gtot_type =
                    let uu____1264 =
                      let uu____1270 =
                        let uu____1271 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1271 in
                      FStar_Util.Inl uu____1270 in
                    FStar_Pervasives_Native.Some uu____1264 in
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
                    uu____1291 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
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
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1462 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1462
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
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
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1491 =
                               let uu____1492 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1495 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1492 uu____1495 in
                             let uu____1498 =
                               let uu____1499 =
                                 let uu____1502 =
                                   let uu____1508 =
                                     let uu____1509 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1509 in
                                   [uu____1508] in
                                 FStar_Syntax_Util.mk_app x uu____1502 in
                               let uu____1510 =
                                 let uu____1513 =
                                   let uu____1519 =
                                     let uu____1520 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1520 in
                                   [uu____1519] in
                                 FStar_Syntax_Util.mk_app y uu____1513 in
                               mk_rel1 b uu____1499 uu____1510 in
                             FStar_Syntax_Util.mk_imp uu____1491 uu____1498 in
                           let uu____1521 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1521)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1524);
                                      FStar_Syntax_Syntax.tk = uu____1525;
                                      FStar_Syntax_Syntax.pos = uu____1526;
                                      FStar_Syntax_Syntax.vars = uu____1527;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1550 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1550
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1553 =
                              let uu____1556 =
                                let uu____1562 =
                                  let uu____1563 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1563 in
                                [uu____1562] in
                              FStar_Syntax_Util.mk_app x uu____1556 in
                            let uu____1564 =
                              let uu____1567 =
                                let uu____1573 =
                                  let uu____1574 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1574 in
                                [uu____1573] in
                              FStar_Syntax_Util.mk_app y uu____1567 in
                            mk_rel1 b uu____1553 uu____1564 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1579 =
                               let uu____1580 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1583 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1580 uu____1583 in
                             let uu____1586 =
                               let uu____1587 =
                                 let uu____1590 =
                                   let uu____1596 =
                                     let uu____1597 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1597 in
                                   [uu____1596] in
                                 FStar_Syntax_Util.mk_app x uu____1590 in
                               let uu____1598 =
                                 let uu____1601 =
                                   let uu____1607 =
                                     let uu____1608 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1608 in
                                   [uu____1607] in
                                 FStar_Syntax_Util.mk_app y uu____1601 in
                               mk_rel1 b uu____1587 uu____1598 in
                             FStar_Syntax_Util.mk_imp uu____1579 uu____1586 in
                           let uu____1609 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1609)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___101_1630 = t1 in
                          let uu____1631 =
                            let uu____1632 =
                              let uu____1640 =
                                let uu____1641 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1641 in
                              ([binder], uu____1640) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1632 in
                          {
                            FStar_Syntax_Syntax.n = uu____1631;
                            FStar_Syntax_Syntax.tk =
                              (uu___101_1630.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___101_1630.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___101_1630.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1653 ->
                        failwith "unhandled arrow"
                    | uu____1661 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1 in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1 in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] env1 t in
                      let uu____1676 =
                        let uu____1677 = FStar_Syntax_Subst.compress t1 in
                        uu____1677.FStar_Syntax_Syntax.n in
                      match uu____1676 with
                      | FStar_Syntax_Syntax.Tm_type uu____1680 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1697 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1697
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1712 =
                                let uu____1713 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1713 i in
                              FStar_Syntax_Syntax.fvar uu____1712
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____1734 =
                            let uu____1738 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1743  ->
                                     match uu____1743 with
                                     | (t2,q) ->
                                         let uu____1748 = project i x in
                                         let uu____1749 = project i y in
                                         mk_stronger t2 uu____1748 uu____1749)
                                args in
                            match uu____1738 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1734 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1766);
                                      FStar_Syntax_Syntax.tk = uu____1767;
                                      FStar_Syntax_Syntax.pos = uu____1768;
                                      FStar_Syntax_Syntax.vars = uu____1769;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1791  ->
                                   match uu____1791 with
                                   | (bv,q) ->
                                       let uu____1796 =
                                         let uu____1797 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1797 in
                                       FStar_Syntax_Syntax.gen_bv uu____1796
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1801 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1801) bvs in
                          let body =
                            let uu____1803 = FStar_Syntax_Util.mk_app x args in
                            let uu____1804 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1803 uu____1804 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1809);
                                      FStar_Syntax_Syntax.tk = uu____1810;
                                      FStar_Syntax_Syntax.pos = uu____1811;
                                      FStar_Syntax_Syntax.vars = uu____1812;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1834  ->
                                   match uu____1834 with
                                   | (bv,q) ->
                                       let uu____1839 =
                                         let uu____1840 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1840 in
                                       FStar_Syntax_Syntax.gen_bv uu____1839
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1844 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1844) bvs in
                          let body =
                            let uu____1846 = FStar_Syntax_Util.mk_app x args in
                            let uu____1847 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1846 uu____1847 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1850 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1852 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1853 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1854 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1852 uu____1853 uu____1854 in
                    let uu____1855 =
                      let uu____1856 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1856 in
                    FStar_Syntax_Util.abs uu____1855 body ret_tot_type in
                  let stronger1 =
                    let uu____1871 = mk_lid "stronger" in
                    register env1 uu____1871 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1877 = FStar_Util.prefix gamma in
                    match uu____1877 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1903 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1903 in
                          let uu____1906 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1906 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____1914 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1914 in
                              let guard_free1 =
                                let uu____1921 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1921 in
                              let pat =
                                let uu____1925 =
                                  let uu____1931 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1931] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1925 in
                              let pattern_guarded_body =
                                let uu____1935 =
                                  let uu____1936 =
                                    let uu____1941 =
                                      let uu____1942 =
                                        let uu____1949 =
                                          let uu____1951 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1951] in
                                        [uu____1949] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1942 in
                                    (body, uu____1941) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1936 in
                                mk1 uu____1935 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1954 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1957 =
                            let uu____1958 =
                              let uu____1959 =
                                let uu____1960 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1963 =
                                  let uu____1969 = args_of_binders1 wp_args in
                                  let uu____1971 =
                                    let uu____1973 =
                                      let uu____1974 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1974 in
                                    [uu____1973] in
                                  FStar_List.append uu____1969 uu____1971 in
                                FStar_Syntax_Util.mk_app uu____1960
                                  uu____1963 in
                              FStar_Syntax_Util.mk_imp equiv uu____1959 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1958 in
                          FStar_Syntax_Util.abs gamma uu____1957
                            ret_gtot_type in
                        let uu____1975 =
                          let uu____1976 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1976 in
                        FStar_Syntax_Util.abs uu____1975 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1983 = mk_lid "wp_ite" in
                    register env1 uu____1983 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1989 = FStar_Util.prefix gamma in
                    match uu____1989 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2013 =
                            let uu____2014 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____2017 =
                              let uu____2023 =
                                let uu____2024 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2024 in
                              [uu____2023] in
                            FStar_Syntax_Util.mk_app uu____2014 uu____2017 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2013 in
                        let uu____2025 =
                          let uu____2026 =
                            let uu____2030 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2030 gamma in
                          FStar_List.append binders uu____2026 in
                        FStar_Syntax_Util.abs uu____2025 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2039 = mk_lid "null_wp" in
                    register env1 uu____2039 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____2048 =
                        let uu____2054 =
                          let uu____2056 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2057 =
                            let uu____2059 =
                              let uu____2062 =
                                let uu____2068 =
                                  let uu____2069 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2069 in
                                [uu____2068] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2062 in
                            let uu____2070 =
                              let uu____2074 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2074] in
                            uu____2059 :: uu____2070 in
                          uu____2056 :: uu____2057 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2054 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2048 in
                    let uu____2077 =
                      let uu____2078 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2078 in
                    FStar_Syntax_Util.abs uu____2077 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2085 = mk_lid "wp_trivial" in
                    register env1 uu____2085 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2090 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2090
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2095 =
                      let uu____2097 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2097 in
                    let uu____2102 =
                      let uu___102_2103 = ed in
                      let uu____2104 =
                        let uu____2105 = c wp_if_then_else2 in
                        ([], uu____2105) in
                      let uu____2107 =
                        let uu____2108 = c wp_ite2 in ([], uu____2108) in
                      let uu____2110 =
                        let uu____2111 = c stronger2 in ([], uu____2111) in
                      let uu____2113 =
                        let uu____2114 = c wp_close2 in ([], uu____2114) in
                      let uu____2116 =
                        let uu____2117 = c wp_assert2 in ([], uu____2117) in
                      let uu____2119 =
                        let uu____2120 = c wp_assume2 in ([], uu____2120) in
                      let uu____2122 =
                        let uu____2123 = c null_wp2 in ([], uu____2123) in
                      let uu____2125 =
                        let uu____2126 = c wp_trivial2 in ([], uu____2126) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___102_2103.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___102_2103.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___102_2103.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___102_2103.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___102_2103.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___102_2103.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___102_2103.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2104;
                        FStar_Syntax_Syntax.ite_wp = uu____2107;
                        FStar_Syntax_Syntax.stronger = uu____2110;
                        FStar_Syntax_Syntax.close_wp = uu____2113;
                        FStar_Syntax_Syntax.assert_p = uu____2116;
                        FStar_Syntax_Syntax.assume_p = uu____2119;
                        FStar_Syntax_Syntax.null_wp = uu____2122;
                        FStar_Syntax_Syntax.trivial = uu____2125;
                        FStar_Syntax_Syntax.repr =
                          (uu___102_2103.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___102_2103.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___102_2103.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___102_2103.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2095, uu____2102)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___103_2138 = dmff_env in
      {
        env = env';
        subst = (uu___103_2138.subst);
        tc_const = (uu___103_2138.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2149 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2161 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___89_2171  ->
    match uu___89_2171 with
    | FStar_Syntax_Syntax.Total (t,uu____2173) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___88_2182  ->
                match uu___88_2182 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2183 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2185 =
          let uu____2186 =
            let uu____2187 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2187 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2186 in
        failwith uu____2185
    | FStar_Syntax_Syntax.GTotal uu____2188 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___90_2196  ->
    match uu___90_2196 with
    | N t ->
        let uu____2198 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2198
    | M t ->
        let uu____2200 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2200
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2204,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2206;
                      FStar_Syntax_Syntax.pos = uu____2207;
                      FStar_Syntax_Syntax.vars = uu____2208;_})
        -> nm_of_comp n2
    | uu____2219 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2231 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2231 with | M uu____2232 -> true | N uu____2233 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2237 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2247 =
        let uu____2251 =
          let uu____2252 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2252 in
        [uu____2251] in
      let uu____2253 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2247 uu____2253 in
    let uu____2256 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2256
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
          (let uu____2291 =
             let uu____2299 =
               let uu____2303 =
                 let uu____2306 =
                   let uu____2307 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2307 in
                 let uu____2308 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2306, uu____2308) in
               [uu____2303] in
             let uu____2313 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2299, uu____2313) in
           FStar_Syntax_Syntax.Tm_arrow uu____2291)
and star_type':
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk1 in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2342) ->
          let binders1 =
            FStar_List.map
              (fun uu____2361  ->
                 match uu____2361 with
                 | (bv,aqual) ->
                     let uu____2368 =
                       let uu___104_2369 = bv in
                       let uu____2370 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___104_2369.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___104_2369.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2370
                       } in
                     (uu____2368, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2373,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2375);
                             FStar_Syntax_Syntax.tk = uu____2376;
                             FStar_Syntax_Syntax.pos = uu____2377;
                             FStar_Syntax_Syntax.vars = uu____2378;_})
               ->
               let uu____2395 =
                 let uu____2396 =
                   let uu____2404 =
                     let uu____2405 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2405 in
                   (binders1, uu____2404) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2396 in
               mk1 uu____2395
           | uu____2409 ->
               let uu____2410 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2410 with
                | N hn ->
                    let uu____2412 =
                      let uu____2413 =
                        let uu____2421 =
                          let uu____2422 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2422 in
                        (binders1, uu____2421) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2413 in
                    mk1 uu____2412
                | M a ->
                    let uu____2427 =
                      let uu____2428 =
                        let uu____2436 =
                          let uu____2440 =
                            let uu____2444 =
                              let uu____2447 =
                                let uu____2448 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2448 in
                              let uu____2449 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2447, uu____2449) in
                            [uu____2444] in
                          FStar_List.append binders1 uu____2440 in
                        let uu____2456 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2436, uu____2456) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2428 in
                    mk1 uu____2427))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2507 = f x in
                    FStar_Util.string_builder_append strb uu____2507);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2511 = f x1 in
                         FStar_Util.string_builder_append strb uu____2511))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2513 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2514 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2513 uu____2514 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2522 =
              let uu____2523 = FStar_Syntax_Subst.compress ty in
              uu____2523.FStar_Syntax_Syntax.n in
            match uu____2522 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2538 =
                  let uu____2539 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2539 in
                if uu____2538
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2553 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2553 s in
                       let uu____2555 =
                         let uu____2556 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2556 in
                       if uu____2555
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2559 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2559 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2570  ->
                                  match uu____2570 with
                                  | (bv,uu____2576) ->
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
            | uu____2589 ->
                ((let uu____2591 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2591);
                 false) in
          let rec is_valid_application head2 =
            let uu____2596 =
              let uu____2597 = FStar_Syntax_Subst.compress head2 in
              uu____2597.FStar_Syntax_Syntax.n in
            match uu____2596 with
            | FStar_Syntax_Syntax.Tm_fvar fv when
                (((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.option_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.either_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq2_lid))
                  ||
                  (let uu____2601 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2601)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2614 -> true
                 | uu____2624 ->
                     ((let uu____2626 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2626);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2627 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2628 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2630) ->
                is_valid_application t2
            | uu____2635 -> false in
          let uu____2636 = is_valid_application head1 in
          if uu____2636
          then
            let uu____2637 =
              let uu____2638 =
                let uu____2648 =
                  FStar_List.map
                    (fun uu____2658  ->
                       match uu____2658 with
                       | (t2,qual) ->
                           let uu____2671 = star_type' env t2 in
                           (uu____2671, qual)) args in
                (head1, uu____2648) in
              FStar_Syntax_Syntax.Tm_app uu____2638 in
            mk1 uu____2637
          else
            (let uu____2678 =
               let uu____2679 =
                 let uu____2680 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2680 in
               FStar_Errors.Err uu____2679 in
             raise uu____2678)
      | FStar_Syntax_Syntax.Tm_bvar uu____2681 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2682 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2683 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2684 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2710 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2710 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___107_2716 = env in
                 let uu____2717 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2717;
                   subst = (uu___107_2716.subst);
                   tc_const = (uu___107_2716.tc_const)
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
               ((let uu___108_2734 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___108_2734.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___108_2734.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2741 =
            let uu____2742 =
              let uu____2747 = star_type' env t2 in (uu____2747, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2742 in
          mk1 uu____2741
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____2785 =
            let uu____2786 =
              let uu____2804 = star_type' env e in
              let uu____2805 =
                let uu____2815 =
                  let uu____2820 = star_type' env t2 in
                  FStar_Util.Inl uu____2820 in
                (uu____2815, FStar_Pervasives_Native.None) in
              (uu____2804, uu____2805, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2786 in
          mk1 uu____2785
      | FStar_Syntax_Syntax.Tm_ascribed uu____2842 ->
          let uu____2860 =
            let uu____2861 =
              let uu____2862 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2862 in
            FStar_Errors.Err uu____2861 in
          raise uu____2860
      | FStar_Syntax_Syntax.Tm_refine uu____2863 ->
          let uu____2868 =
            let uu____2869 =
              let uu____2870 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2870 in
            FStar_Errors.Err uu____2869 in
          raise uu____2868
      | FStar_Syntax_Syntax.Tm_uinst uu____2871 ->
          let uu____2876 =
            let uu____2877 =
              let uu____2878 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2878 in
            FStar_Errors.Err uu____2877 in
          raise uu____2876
      | FStar_Syntax_Syntax.Tm_constant uu____2879 ->
          let uu____2880 =
            let uu____2881 =
              let uu____2882 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2882 in
            FStar_Errors.Err uu____2881 in
          raise uu____2880
      | FStar_Syntax_Syntax.Tm_match uu____2883 ->
          let uu____2899 =
            let uu____2900 =
              let uu____2901 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2901 in
            FStar_Errors.Err uu____2900 in
          raise uu____2899
      | FStar_Syntax_Syntax.Tm_let uu____2902 ->
          let uu____2910 =
            let uu____2911 =
              let uu____2912 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2912 in
            FStar_Errors.Err uu____2911 in
          raise uu____2910
      | FStar_Syntax_Syntax.Tm_uvar uu____2913 ->
          let uu____2922 =
            let uu____2923 =
              let uu____2924 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2924 in
            FStar_Errors.Err uu____2923 in
          raise uu____2922
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2925 =
            let uu____2926 =
              let uu____2927 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2927 in
            FStar_Errors.Err uu____2926 in
          raise uu____2925
      | FStar_Syntax_Syntax.Tm_delayed uu____2928 -> failwith "impossible"
let is_monadic uu___92_2961 =
  match uu___92_2961 with
  | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
  | FStar_Pervasives_Native.Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____2973;
        FStar_Syntax_Syntax.res_typ = uu____2974;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____2976;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_2993  ->
              match uu___91_2993 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____2994 -> false))
  | FStar_Pervasives_Native.Some (FStar_Util.Inr (uu____2995,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___91_3008  ->
              match uu___91_3008 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3009 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3013 =
      let uu____3014 = FStar_Syntax_Subst.compress t in
      uu____3014.FStar_Syntax_Syntax.n in
    match uu____3013 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3034 =
            let uu____3035 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____3035 in
          is_C uu____3034 in
        if r
        then
          ((let uu____3047 =
              let uu____3048 =
                FStar_List.for_all
                  (fun uu____3051  ->
                     match uu____3051 with | (h,uu____3055) -> is_C h) args in
              Prims.op_Negation uu____3048 in
            if uu____3047 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3059 =
              let uu____3060 =
                FStar_List.for_all
                  (fun uu____3063  ->
                     match uu____3063 with
                     | (h,uu____3067) ->
                         let uu____3068 = is_C h in
                         Prims.op_Negation uu____3068) args in
              Prims.op_Negation uu____3060 in
            if uu____3059 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3082 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3082 with
         | M t1 ->
             ((let uu____3085 = is_C t1 in
               if uu____3085 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3089) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3095) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3101,uu____3102) -> is_C t1
    | uu____3131 -> false
let mk_return:
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk1 env t in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type in
        let body =
          let uu____3158 =
            let uu____3159 =
              let uu____3169 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3170 =
                let uu____3174 =
                  let uu____3177 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3177) in
                [uu____3174] in
              (uu____3169, uu____3170) in
            FStar_Syntax_Syntax.Tm_app uu____3159 in
          mk1 uu____3158 in
        let uu____3185 =
          let uu____3186 = FStar_Syntax_Syntax.mk_binder p in [uu____3186] in
        let uu____3187 =
          let uu____3194 =
            let uu____3200 =
              let uu____3201 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3201 in
            FStar_Util.Inl uu____3200 in
          FStar_Pervasives_Native.Some uu____3194 in
        FStar_Syntax_Util.abs uu____3185 body uu____3187
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___93_3214  ->
    match uu___93_3214 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3215 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3349 =
          match uu____3349 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3370 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3371 =
                       let uu____3372 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3372 in
                     Prims.op_Negation uu____3371) in
                if uu____3370
                then
                  let uu____3373 =
                    let uu____3374 =
                      let uu____3375 = FStar_Syntax_Print.term_to_string e in
                      let uu____3376 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3377 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3375 uu____3376 uu____3377 in
                    FStar_Errors.Err uu____3374 in
                  raise uu____3373
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3391 = mk_return env t1 s_e in
                     ((M t1), uu____3391, u_e)))
               | (M t1,N t2) ->
                   let uu____3394 =
                     let uu____3395 =
                       let uu____3396 = FStar_Syntax_Print.term_to_string e in
                       let uu____3397 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3398 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3396 uu____3397 uu____3398 in
                     FStar_Errors.Err uu____3395 in
                   raise uu____3394) in
        let ensure_m env1 e2 =
          let strip_m uu___94_3424 =
            match uu___94_3424 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3434 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3445 =
                let uu____3446 =
                  let uu____3449 =
                    let uu____3450 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3450 in
                  (uu____3449, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3446 in
              raise uu____3445
          | M uu____3454 ->
              let uu____3455 = check env1 e2 context_nm in strip_m uu____3455 in
        let uu____3459 =
          let uu____3460 = FStar_Syntax_Subst.compress e in
          uu____3460.FStar_Syntax_Syntax.n in
        match uu____3459 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3466 ->
            let uu____3467 = infer env e in return_if uu____3467
        | FStar_Syntax_Syntax.Tm_name uu____3471 ->
            let uu____3472 = infer env e in return_if uu____3472
        | FStar_Syntax_Syntax.Tm_fvar uu____3476 ->
            let uu____3477 = infer env e in return_if uu____3477
        | FStar_Syntax_Syntax.Tm_abs uu____3481 ->
            let uu____3496 = infer env e in return_if uu____3496
        | FStar_Syntax_Syntax.Tm_constant uu____3500 ->
            let uu____3501 = infer env e in return_if uu____3501
        | FStar_Syntax_Syntax.Tm_app uu____3505 ->
            let uu____3515 = infer env e in return_if uu____3515
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3562) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3568) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3574,uu____3575) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3604 ->
            let uu____3612 =
              let uu____3613 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3613 in
            failwith uu____3612
        | FStar_Syntax_Syntax.Tm_type uu____3617 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3621 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3632 ->
            let uu____3637 =
              let uu____3638 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3638 in
            failwith uu____3637
        | FStar_Syntax_Syntax.Tm_uvar uu____3642 ->
            let uu____3651 =
              let uu____3652 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3652 in
            failwith uu____3651
        | FStar_Syntax_Syntax.Tm_delayed uu____3656 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3680 =
              let uu____3681 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3681 in
            failwith uu____3680
and infer:
  env ->
    FStar_Syntax_Syntax.term ->
      (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env in
      let uu____3703 =
        let uu____3704 = FStar_Syntax_Subst.compress e in
        uu____3704.FStar_Syntax_Syntax.n in
      match uu____3703 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___109_3744 = env in
            let uu____3745 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3745;
              subst = (uu___109_3744.subst);
              tc_const = (uu___109_3744.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3754  ->
                 match uu____3754 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___110_3762 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___110_3762.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___110_3762.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3763 =
            FStar_List.fold_left
              (fun uu____3772  ->
                 fun uu____3773  ->
                   match (uu____3772, uu____3773) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3801 = is_C c in
                       if uu____3801
                       then
                         let xw =
                           let uu____3806 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____3806 in
                         let x =
                           let uu___111_3808 = bv in
                           let uu____3809 =
                             let uu____3812 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3812 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___111_3808.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___111_3808.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3809
                           } in
                         let env3 =
                           let uu___112_3814 = env2 in
                           let uu____3815 =
                             let uu____3817 =
                               let uu____3818 =
                                 let uu____3823 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3823) in
                               FStar_Syntax_Syntax.NT uu____3818 in
                             uu____3817 :: (env2.subst) in
                           {
                             env = (uu___112_3814.env);
                             subst = uu____3815;
                             tc_const = (uu___112_3814.tc_const)
                           } in
                         let uu____3824 =
                           let uu____3826 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3827 =
                             let uu____3829 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3829 :: acc in
                           uu____3826 :: uu____3827 in
                         (env3, uu____3824)
                       else
                         (let x =
                            let uu___113_3833 = bv in
                            let uu____3834 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___113_3833.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___113_3833.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3834
                            } in
                          let uu____3837 =
                            let uu____3839 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3839 :: acc in
                          (env2, uu____3837))) (env1, []) binders1 in
          (match uu____3763 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3851 =
                 let check_what =
                   let uu____3863 = is_monadic what in
                   if uu____3863 then check_m else check_n in
                 let uu____3872 = check_what env2 body1 in
                 match uu____3872 with
                 | (t,s_body,u_body) ->
                     let uu____3882 =
                       let uu____3883 =
                         let uu____3884 = is_monadic what in
                         if uu____3884 then M t else N t in
                       comp_of_nm uu____3883 in
                     (uu____3882, s_body, u_body) in
               (match uu____3851 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
                          let uu____3927 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___95_3929  ->
                                    match uu___95_3929 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3930 -> false)) in
                          if uu____3927
                          then
                            let double_starred_comp =
                              let uu____3938 =
                                let uu____3939 =
                                  let uu____3940 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____3940 in
                                FStar_All.pipe_left double_star uu____3939 in
                              FStar_Syntax_Syntax.mk_Total uu____3938 in
                            let flags =
                              FStar_List.filter
                                (fun uu___96_3945  ->
                                   match uu___96_3945 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3946 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____3947 =
                              let uu____3953 =
                                let uu____3954 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____3954 in
                              FStar_Util.Inl uu____3953 in
                            FStar_Pervasives_Native.Some uu____3947
                          else
                            FStar_Pervasives_Native.Some
                              (FStar_Util.Inl
                                 ((let uu___114_3974 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___114_3974.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___114_3974.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___114_3974.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____3975  ->
                                          let c =
                                            lc.FStar_Syntax_Syntax.comp () in
                                          let result_typ =
                                            star_type' env2
                                              (FStar_Syntax_Util.comp_result
                                                 c) in
                                          FStar_Syntax_Util.set_result_typ c
                                            result_typ)
                                   })))
                      | FStar_Pervasives_Native.Some (FStar_Util.Inr
                          (lid,flags)) ->
                          let uu____3992 =
                            let uu____3998 =
                              let uu____4002 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___97_4004  ->
                                        match uu___97_4004 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4005 -> false)) in
                              if uu____4002
                              then
                                let uu____4009 =
                                  FStar_List.filter
                                    (fun uu___98_4011  ->
                                       match uu___98_4011 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4012 -> true) flags in
                                (FStar_Parser_Const.effect_Tot_lid,
                                  uu____4009)
                              else (lid, flags) in
                            FStar_Util.Inr uu____3998 in
                          FStar_Pervasives_Native.Some uu____3992 in
                    let uu____4024 =
                      let comp1 =
                        let uu____4036 = is_monadic what in
                        let uu____4037 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4036 uu____4037 in
                      let uu____4038 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____4038,
                        (FStar_Pervasives_Native.Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4024 with
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
                FStar_Syntax_Syntax.ty = uu____4116;
                FStar_Syntax_Syntax.p = uu____4117;_};
            FStar_Syntax_Syntax.fv_delta = uu____4118;
            FStar_Syntax_Syntax.fv_qual = uu____4119;_}
          ->
          let uu____4125 =
            let uu____4128 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____4128 in
          (match uu____4125 with
           | (uu____4144,t) ->
               let uu____4146 = let uu____4147 = normalize1 t in N uu____4147 in
               (uu____4146, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4164 = check_n env head1 in
          (match uu____4164 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4178 =
                   let uu____4179 = FStar_Syntax_Subst.compress t in
                   uu____4179.FStar_Syntax_Syntax.n in
                 match uu____4178 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4182 -> true
                 | uu____4190 -> false in
               let rec flatten1 t =
                 let uu____4202 =
                   let uu____4203 = FStar_Syntax_Subst.compress t in
                   uu____4203.FStar_Syntax_Syntax.n in
                 match uu____4202 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4215);
                                FStar_Syntax_Syntax.tk = uu____4216;
                                FStar_Syntax_Syntax.pos = uu____4217;
                                FStar_Syntax_Syntax.vars = uu____4218;_})
                     when is_arrow t1 ->
                     let uu____4235 = flatten1 t1 in
                     (match uu____4235 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4287,uu____4288)
                     -> flatten1 e1
                 | uu____4317 ->
                     let uu____4318 =
                       let uu____4319 =
                         let uu____4320 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4320 in
                       FStar_Errors.Err uu____4319 in
                     raise uu____4318 in
               let uu____4328 = flatten1 t_head in
               (match uu____4328 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4373 =
                          let uu____4374 =
                            let uu____4375 = FStar_Util.string_of_int n1 in
                            let uu____4379 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4385 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4375 uu____4379 uu____4385 in
                          FStar_Errors.Err uu____4374 in
                        raise uu____4373)
                     else ();
                     (let uu____4390 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4390 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4417 args1 =
                            match uu____4417 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4460 =
                                       let uu____4461 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4461.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4460
                                 | (binders3,[]) ->
                                     let uu____4480 =
                                       let uu____4481 =
                                         let uu____4484 =
                                           let uu____4485 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4485 in
                                         FStar_Syntax_Subst.compress
                                           uu____4484 in
                                       uu____4481.FStar_Syntax_Syntax.n in
                                     (match uu____4480 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4501 =
                                            let uu____4502 =
                                              let uu____4503 =
                                                let uu____4511 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4511) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4503 in
                                            mk1 uu____4502 in
                                          N uu____4501
                                      | uu____4515 -> failwith "wat?")
                                 | ([],uu____4516::uu____4517) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4542)::binders3,(arg,uu____4545)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4579 = FStar_List.splitAt n' binders1 in
                          (match uu____4579 with
                           | (binders2,uu____4596) ->
                               let uu____4609 =
                                 let uu____4619 =
                                   FStar_List.map2
                                     (fun uu____4639  ->
                                        fun uu____4640  ->
                                          match (uu____4639, uu____4640) with
                                          | ((bv,uu____4657),(arg,q)) ->
                                              let uu____4664 =
                                                let uu____4665 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4665.FStar_Syntax_Syntax.n in
                                              (match uu____4664 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4675 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4688 ->
                                                   let uu____4689 =
                                                     check_n env arg in
                                                   (match uu____4689 with
                                                    | (uu____4700,s_arg,u_arg)
                                                        ->
                                                        let uu____4703 =
                                                          let uu____4707 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4707
                                                          then
                                                            let uu____4711 =
                                                              let uu____4714
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4714, q) in
                                                            [uu____4711;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4703))))
                                     binders2 args in
                                 FStar_List.split uu____4619 in
                               (match uu____4609 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4761 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4767 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4761, uu____4767)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4816) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4822) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4828,uu____4829) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4859 = let uu____4860 = env.tc_const c in N uu____4860 in
          (uu____4859, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4861 ->
          let uu____4869 =
            let uu____4870 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4870 in
          failwith uu____4869
      | FStar_Syntax_Syntax.Tm_type uu____4874 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4878 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4889 ->
          let uu____4894 =
            let uu____4895 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4895 in
          failwith uu____4894
      | FStar_Syntax_Syntax.Tm_uvar uu____4899 ->
          let uu____4908 =
            let uu____4909 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4909 in
          failwith uu____4908
      | FStar_Syntax_Syntax.Tm_delayed uu____4913 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4937 =
            let uu____4938 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4938 in
          failwith uu____4937
and mk_match:
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.withinfo_t,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                          FStar_Syntax_Syntax.syntax
                                          FStar_Pervasives_Native.option,
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos in
          let uu____4976 = check_n env e0 in
          match uu____4976 with
          | (uu____4983,s_e0,u_e0) ->
              let uu____4986 =
                let uu____5004 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5037 = FStar_Syntax_Subst.open_branch b in
                       match uu____5037 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___115_5069 = env in
                             let uu____5070 =
                               let uu____5071 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5071 in
                             {
                               env = uu____5070;
                               subst = (uu___115_5069.subst);
                               tc_const = (uu___115_5069.tc_const)
                             } in
                           let uu____5073 = f env1 body in
                           (match uu____5073 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____5122 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5004 in
              (match uu____4986 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5187 = FStar_List.hd nms in
                     match uu____5187 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___99_5191  ->
                          match uu___99_5191 with
                          | M uu____5192 -> true
                          | uu____5193 -> false) nms in
                   let uu____5194 =
                     let uu____5217 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5269  ->
                              match uu____5269 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5392 =
                                         check env original_body (M t2) in
                                       (match uu____5392 with
                                        | (uu____5415,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5444,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5217 in
                   (match uu____5194 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5563  ->
                                 match uu____5563 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5604 =
                                         let uu____5605 =
                                           let uu____5615 =
                                             let uu____5619 =
                                               let uu____5622 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5623 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5622, uu____5623) in
                                             [uu____5619] in
                                           (s_body, uu____5615) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5605 in
                                       mk1 uu____5604 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5645 =
                              let uu____5646 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5646] in
                            let uu____5647 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5649 =
                              let uu____5656 =
                                let uu____5662 =
                                  let uu____5663 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5663 in
                                FStar_Util.Inl uu____5662 in
                              FStar_Pervasives_Native.Some uu____5656 in
                            FStar_Syntax_Util.abs uu____5645 uu____5647
                              uu____5649 in
                          let t1_star =
                            let uu____5677 =
                              let uu____5681 =
                                let uu____5682 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5682 in
                              [uu____5681] in
                            let uu____5683 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5677 uu____5683 in
                          let uu____5686 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____5716 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5686, uu____5716)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5730 =
                             let uu____5733 =
                               let uu____5734 =
                                 let uu____5752 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5752,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5734 in
                             mk1 uu____5733 in
                           let uu____5779 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5730, uu____5779))))
and mk_let:
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
                 FStar_Pervasives_Native.tuple3)
            ->
            (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos in
            let e1 = binding.FStar_Syntax_Syntax.lbdef in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname in
            let x_binders =
              let uu____5822 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5822] in
            let uu____5823 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5823 with
            | (x_binders1,e21) ->
                let uu____5831 = infer env e1 in
                (match uu____5831 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5842 = is_C t1 in
                       if uu____5842
                       then
                         let uu___116_5843 = binding in
                         let uu____5844 =
                           let uu____5847 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5847 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___116_5843.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___116_5843.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5844;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___116_5843.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___116_5843.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___117_5850 = env in
                       let uu____5851 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___118_5852 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___118_5852.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___118_5852.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5851;
                         subst = (uu___117_5850.subst);
                         tc_const = (uu___117_5850.tc_const)
                       } in
                     let uu____5853 = proceed env1 e21 in
                     (match uu____5853 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___119_5864 = binding in
                            let uu____5865 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___119_5864.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___119_5864.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5865;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___119_5864.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___119_5864.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5868 =
                            let uu____5871 =
                              let uu____5872 =
                                let uu____5880 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___120_5885 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___120_5885.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___120_5885.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___120_5885.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___120_5885.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5880) in
                              FStar_Syntax_Syntax.Tm_let uu____5872 in
                            mk1 uu____5871 in
                          let uu____5886 =
                            let uu____5889 =
                              let uu____5890 =
                                let uu____5898 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___121_5903 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5903.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5903.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5903.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5903.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5898) in
                              FStar_Syntax_Syntax.Tm_let uu____5890 in
                            mk1 uu____5889 in
                          (nm_rec, uu____5868, uu____5886))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___122_5912 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___122_5912.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___122_5912.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___122_5912.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___123_5914 = env in
                       let uu____5915 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___124_5916 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_5916.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_5916.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5915;
                         subst = (uu___123_5914.subst);
                         tc_const = (uu___123_5914.tc_const)
                       } in
                     let uu____5917 = ensure_m env1 e21 in
                     (match uu____5917 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____5934 =
                              let uu____5935 =
                                let uu____5945 =
                                  let uu____5949 =
                                    let uu____5952 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5953 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5952, uu____5953) in
                                  [uu____5949] in
                                (s_e2, uu____5945) in
                              FStar_Syntax_Syntax.Tm_app uu____5935 in
                            mk1 uu____5934 in
                          let s_e22 =
                            let uu____5962 =
                              let uu____5969 =
                                let uu____5975 =
                                  let uu____5976 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5976 in
                                FStar_Util.Inl uu____5975 in
                              FStar_Pervasives_Native.Some uu____5969 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____5962 in
                          let body =
                            let uu____5990 =
                              let uu____5991 =
                                let uu____6001 =
                                  let uu____6005 =
                                    let uu____6008 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6008) in
                                  [uu____6005] in
                                (s_e1, uu____6001) in
                              FStar_Syntax_Syntax.Tm_app uu____5991 in
                            mk1 uu____5990 in
                          let uu____6016 =
                            let uu____6017 =
                              let uu____6018 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6018] in
                            let uu____6019 =
                              let uu____6026 =
                                let uu____6032 =
                                  let uu____6033 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6033 in
                                FStar_Util.Inl uu____6032 in
                              FStar_Pervasives_Native.Some uu____6026 in
                            FStar_Syntax_Util.abs uu____6017 body uu____6019 in
                          let uu____6044 =
                            let uu____6047 =
                              let uu____6048 =
                                let uu____6056 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___125_6061 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___125_6061.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___125_6061.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___125_6061.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___125_6061.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6056) in
                              FStar_Syntax_Syntax.Tm_let uu____6048 in
                            mk1 uu____6047 in
                          ((M t2), uu____6016, uu____6044)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6070 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____6070 in
      let uu____6075 = check env e mn in
      match uu____6075 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6085 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6098 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____6098 in
      let uu____6103 = check env e mn in
      match uu____6103 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6113 -> failwith "[check_m]: impossible"
and comp_of_nm: nm_ -> FStar_Syntax_Syntax.comp =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t
and mk_M: FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp =
  fun t  ->
    FStar_Syntax_Syntax.mk_Comp
      {
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.monadic_lid;
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
        (let uu____6135 =
           let uu____6136 = is_C c in Prims.op_Negation uu____6136 in
         if uu____6135 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____6148 =
           let uu____6149 = FStar_Syntax_Subst.compress c in
           uu____6149.FStar_Syntax_Syntax.n in
         match uu____6148 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6168 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6168 with
              | (wp_head,wp_args) ->
                  ((let uu____6195 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6208 =
                           let uu____6209 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6209 in
                         Prims.op_Negation uu____6208) in
                    if uu____6195 then failwith "mismatch" else ());
                   (let uu____6218 =
                      let uu____6219 =
                        let uu____6229 =
                          FStar_List.map2
                            (fun uu____6239  ->
                               fun uu____6240  ->
                                 match (uu____6239, uu____6240) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6263 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6263
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6266 = print_implicit q in
                                         let uu____6267 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6266 uu____6267)
                                      else ();
                                      (let uu____6269 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6269, q)))) args wp_args in
                        (head1, uu____6229) in
                      FStar_Syntax_Syntax.Tm_app uu____6219 in
                    mk1 uu____6218)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6291 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6291 with
              | (binders_orig,comp1) ->
                  let uu____6296 =
                    let uu____6304 =
                      FStar_List.map
                        (fun uu____6318  ->
                           match uu____6318 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6331 = is_C h in
                               if uu____6331
                               then
                                 let w' =
                                   let uu____6338 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____6338 in
                                 let uu____6339 =
                                   let uu____6343 =
                                     let uu____6347 =
                                       let uu____6350 =
                                         let uu____6351 =
                                           let uu____6352 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6352 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6351 in
                                       (uu____6350, q) in
                                     [uu____6347] in
                                   (w', q) :: uu____6343 in
                                 (w', uu____6339)
                               else
                                 (let x =
                                    let uu____6364 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____6364 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6304 in
                  (match uu____6296 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6394 =
                           let uu____6396 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6396 in
                         FStar_Syntax_Subst.subst_comp uu____6394 comp1 in
                       let app =
                         let uu____6400 =
                           let uu____6401 =
                             let uu____6411 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6418 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6419 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6418, uu____6419)) bvs in
                             (wp, uu____6411) in
                           FStar_Syntax_Syntax.Tm_app uu____6401 in
                         mk1 uu____6400 in
                       let comp3 =
                         let uu____6424 = type_of_comp comp2 in
                         let uu____6425 = is_monadic_comp comp2 in
                         trans_G env uu____6424 uu____6425 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6427,uu____6428) ->
             trans_F_ env e wp
         | uu____6457 -> failwith "impossible trans_F_")
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
            let uu____6462 =
              let uu____6463 = star_type' env h in
              let uu____6466 =
                let uu____6472 =
                  let uu____6475 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6475) in
                [uu____6472] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6463;
                FStar_Syntax_Syntax.effect_args = uu____6466;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6462
          else
            (let uu____6481 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6481)
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
    fun t  -> let uu____6492 = n env.env t in star_type' env uu____6492
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____6504 = n env.env t in check_n env uu____6504
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6514 = n env.env c in
        let uu____6515 = n env.env wp in trans_F_ env uu____6514 uu____6515