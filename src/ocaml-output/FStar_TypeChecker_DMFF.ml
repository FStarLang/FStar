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
              let uu___97_64 = a in
              let uu____65 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___97_64.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___97_64.FStar_Syntax_Syntax.index);
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
             let mk_lid name =
               FStar_Ident.lid_of_path
                 (FStar_Ident.path_of_text
                    (Prims.strcat
                       (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname)
                       (Prims.strcat "_" name))) FStar_Range.dummyRange in
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
                      let uu____292 =
                        let uu____296 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____297 =
                          let uu____299 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____299] in
                        uu____296 :: uu____297 in
                      FStar_List.append binders uu____292 in
                    FStar_Syntax_Util.abs uu____288 body None in
                  let uu____307 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____308 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____307, uu____308) in
                match uu____265 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____339 =
                        let uu____340 =
                          let uu____350 =
                            let uu____354 =
                              FStar_List.map
                                (fun uu____362  ->
                                   match uu____362 with
                                   | (bv,uu____368) ->
                                       let uu____369 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____370 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____369, uu____370)) binders in
                            let uu____371 =
                              let uu____375 =
                                let uu____378 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____379 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____378, uu____379) in
                              let uu____380 =
                                let uu____384 =
                                  let uu____387 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____387) in
                                [uu____384] in
                              uu____375 :: uu____380 in
                            FStar_List.append uu____354 uu____371 in
                          (fv, uu____350) in
                        FStar_Syntax_Syntax.Tm_app uu____340 in
                      mk1 uu____339 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____253 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____433 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____433 in
                    let ret1 =
                      let uu____441 =
                        let uu____447 =
                          let uu____448 =
                            let uu____451 =
                              let uu____452 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____452 in
                            FStar_Syntax_Syntax.mk_Total uu____451 in
                          FStar_Syntax_Util.lcomp_of_comp uu____448 in
                        FStar_Util.Inl uu____447 in
                      Some uu____441 in
                    let body =
                      let uu____462 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____462 ret1 in
                    let uu____463 =
                      let uu____467 = mk_all_implicit binders in
                      let uu____471 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____467 uu____471 in
                    FStar_Syntax_Util.abs uu____463 body ret1 in
                  let c_pure1 =
                    let uu____486 = mk_lid "pure" in
                    register env1 uu____486 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____491 =
                        let uu____492 =
                          let uu____493 =
                            let uu____497 =
                              let uu____498 =
                                let uu____499 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____499 in
                              FStar_Syntax_Syntax.mk_binder uu____498 in
                            [uu____497] in
                          let uu____500 =
                            let uu____503 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____503 in
                          FStar_Syntax_Util.arrow uu____493 uu____500 in
                        mk_gctx uu____492 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____491 in
                    let r =
                      let uu____505 =
                        let uu____506 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____506 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____505 in
                    let ret1 =
                      let uu____514 =
                        let uu____520 =
                          let uu____521 =
                            let uu____524 =
                              let uu____525 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____525 in
                            FStar_Syntax_Syntax.mk_Total uu____524 in
                          FStar_Syntax_Util.lcomp_of_comp uu____521 in
                        FStar_Util.Inl uu____520 in
                      Some uu____514 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____540 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____543 =
                          let uu____549 =
                            let uu____551 =
                              let uu____552 =
                                let uu____553 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____553
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____552 in
                            [uu____551] in
                          FStar_List.append gamma_as_args uu____549 in
                        FStar_Syntax_Util.mk_app uu____540 uu____543 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____556 =
                      let uu____560 = mk_all_implicit binders in
                      let uu____564 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____560 uu____564 in
                    FStar_Syntax_Util.abs uu____556 outer_body ret1 in
                  let c_app1 =
                    let uu____583 = mk_lid "app" in
                    register env1 uu____583 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____590 =
                        let uu____594 =
                          let uu____595 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____595 in
                        [uu____594] in
                      let uu____596 =
                        let uu____599 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____599 in
                      FStar_Syntax_Util.arrow uu____590 uu____596 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____602 =
                        let uu____603 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____603 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____602 in
                    let ret1 =
                      let uu____611 =
                        let uu____617 =
                          let uu____618 =
                            let uu____621 =
                              let uu____622 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____622 in
                            FStar_Syntax_Syntax.mk_Total uu____621 in
                          FStar_Syntax_Util.lcomp_of_comp uu____618 in
                        FStar_Util.Inl uu____617 in
                      Some uu____611 in
                    let uu____631 =
                      let uu____635 = mk_all_implicit binders in
                      let uu____639 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____635 uu____639 in
                    let uu____657 =
                      let uu____658 =
                        let uu____664 =
                          let uu____666 =
                            let uu____669 =
                              let uu____675 =
                                let uu____677 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____677] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____675 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____669 in
                          let uu____678 =
                            let uu____682 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____682] in
                          uu____666 :: uu____678 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____664 in
                      FStar_Syntax_Util.mk_app c_app1 uu____658 in
                    FStar_Syntax_Util.abs uu____631 uu____657 ret1 in
                  let c_lift11 =
                    let uu____686 = mk_lid "lift1" in
                    register env1 uu____686 c_lift1 in
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
                      let uu____694 =
                        let uu____698 =
                          let uu____699 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____699 in
                        let uu____700 =
                          let uu____702 =
                            let uu____703 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____703 in
                          [uu____702] in
                        uu____698 :: uu____700 in
                      let uu____704 =
                        let uu____707 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____707 in
                      FStar_Syntax_Util.arrow uu____694 uu____704 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____710 =
                        let uu____711 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____711 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____710 in
                    let a2 =
                      let uu____713 =
                        let uu____714 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____714 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____713 in
                    let ret1 =
                      let uu____722 =
                        let uu____728 =
                          let uu____729 =
                            let uu____732 =
                              let uu____733 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____733 in
                            FStar_Syntax_Syntax.mk_Total uu____732 in
                          FStar_Syntax_Util.lcomp_of_comp uu____729 in
                        FStar_Util.Inl uu____728 in
                      Some uu____722 in
                    let uu____742 =
                      let uu____746 = mk_all_implicit binders in
                      let uu____750 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____746 uu____750 in
                    let uu____772 =
                      let uu____773 =
                        let uu____779 =
                          let uu____781 =
                            let uu____784 =
                              let uu____790 =
                                let uu____792 =
                                  let uu____795 =
                                    let uu____801 =
                                      let uu____803 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____803] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____801 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____795 in
                                let uu____804 =
                                  let uu____808 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____808] in
                                uu____792 :: uu____804 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____790 in
                            FStar_Syntax_Util.mk_app c_app1 uu____784 in
                          let uu____811 =
                            let uu____815 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____815] in
                          uu____781 :: uu____811 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____779 in
                      FStar_Syntax_Util.mk_app c_app1 uu____773 in
                    FStar_Syntax_Util.abs uu____742 uu____772 ret1 in
                  let c_lift21 =
                    let uu____819 = mk_lid "lift2" in
                    register env1 uu____819 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____826 =
                        let uu____830 =
                          let uu____831 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____831 in
                        [uu____830] in
                      let uu____832 =
                        let uu____835 =
                          let uu____836 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____836 in
                        FStar_Syntax_Syntax.mk_Total uu____835 in
                      FStar_Syntax_Util.arrow uu____826 uu____832 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____845 =
                        let uu____851 =
                          let uu____852 =
                            let uu____855 =
                              let uu____856 =
                                let uu____857 =
                                  let uu____861 =
                                    let uu____862 =
                                      FStar_Syntax_Syntax.bv_to_name t1 in
                                    FStar_Syntax_Syntax.null_binder uu____862 in
                                  [uu____861] in
                                let uu____863 =
                                  let uu____866 =
                                    FStar_Syntax_Syntax.bv_to_name t2 in
                                  FStar_Syntax_Syntax.mk_GTotal uu____866 in
                                FStar_Syntax_Util.arrow uu____857 uu____863 in
                              mk_ctx uu____856 in
                            FStar_Syntax_Syntax.mk_Total uu____855 in
                          FStar_Syntax_Util.lcomp_of_comp uu____852 in
                        FStar_Util.Inl uu____851 in
                      Some uu____845 in
                    let e1 =
                      let uu____876 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____876 in
                    let body =
                      let uu____878 =
                        let uu____882 =
                          let uu____886 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____886] in
                        FStar_List.append gamma uu____882 in
                      let uu____889 =
                        let uu____890 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____893 =
                          let uu____899 =
                            let uu____900 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____900 in
                          let uu____901 = args_of_binders1 gamma in uu____899
                            :: uu____901 in
                        FStar_Syntax_Util.mk_app uu____890 uu____893 in
                      FStar_Syntax_Util.abs uu____878 uu____889 ret1 in
                    let uu____903 =
                      let uu____907 = mk_all_implicit binders in
                      let uu____911 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____907 uu____911 in
                    FStar_Syntax_Util.abs uu____903 body ret1 in
                  let c_push1 =
                    let uu____928 = mk_lid "push" in
                    register env1 uu____928 c_push in
                  let ret_tot_wp_a =
                    let uu____936 =
                      let uu____942 =
                        let uu____943 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____943 in
                      FStar_Util.Inl uu____942 in
                    Some uu____936 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____971 =
                        let uu____972 =
                          let uu____982 = args_of_binders1 binders in
                          (c, uu____982) in
                        FStar_Syntax_Syntax.Tm_app uu____972 in
                      mk1 uu____971
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____990 =
                        let uu____991 =
                          let uu____995 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____996 =
                            let uu____998 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____998] in
                          uu____995 :: uu____996 in
                        let uu____999 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____991 uu____999 in
                      FStar_Syntax_Syntax.mk_Total uu____990 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____1003 =
                      let uu____1007 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1007 in
                    let uu____1013 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____1015 =
                        let uu____1018 =
                          let uu____1024 =
                            let uu____1026 =
                              let uu____1029 =
                                let uu____1035 =
                                  let uu____1036 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1036 in
                                [uu____1035] in
                              FStar_Syntax_Util.mk_app l_ite uu____1029 in
                            [uu____1026] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1024 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1018 in
                      FStar_Syntax_Util.ascribe uu____1015
                        (FStar_Util.Inr result_comp) in
                    FStar_Syntax_Util.abs uu____1003 uu____1013
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1052 = mk_lid "wp_if_then_else" in
                    register env1 uu____1052 wp_if_then_else in
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
                      let uu____1063 =
                        let uu____1069 =
                          let uu____1071 =
                            let uu____1074 =
                              let uu____1080 =
                                let uu____1082 =
                                  let uu____1085 =
                                    let uu____1091 =
                                      let uu____1092 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1092 in
                                    [uu____1091] in
                                  FStar_Syntax_Util.mk_app l_and uu____1085 in
                                [uu____1082] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1080 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1074 in
                          let uu____1097 =
                            let uu____1101 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1101] in
                          uu____1071 :: uu____1097 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1069 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1063 in
                    let uu____1104 =
                      let uu____1108 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1108 in
                    FStar_Syntax_Util.abs uu____1104 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1115 = mk_lid "wp_assert" in
                    register env1 uu____1115 wp_assert in
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
                      let uu____1126 =
                        let uu____1132 =
                          let uu____1134 =
                            let uu____1137 =
                              let uu____1143 =
                                let uu____1145 =
                                  let uu____1148 =
                                    let uu____1154 =
                                      let uu____1155 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1155 in
                                    [uu____1154] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1148 in
                                [uu____1145] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1143 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1137 in
                          let uu____1160 =
                            let uu____1164 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1164] in
                          uu____1134 :: uu____1160 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1132 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1126 in
                    let uu____1167 =
                      let uu____1171 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1171 in
                    FStar_Syntax_Util.abs uu____1167 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1178 = mk_lid "wp_assume" in
                    register env1 uu____1178 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1187 =
                        let uu____1191 =
                          let uu____1192 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1192 in
                        [uu____1191] in
                      let uu____1193 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1187 uu____1193 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1200 =
                        let uu____1206 =
                          let uu____1208 =
                            let uu____1211 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1211 in
                          let uu____1217 =
                            let uu____1221 =
                              let uu____1224 =
                                let uu____1230 =
                                  let uu____1232 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1232] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1230 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1224 in
                            [uu____1221] in
                          uu____1208 :: uu____1217 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1206 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1200 in
                    let uu____1239 =
                      let uu____1243 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1243 in
                    FStar_Syntax_Util.abs uu____1239 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1250 = mk_lid "wp_close" in
                    register env1 uu____1250 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1261 =
                      let uu____1267 =
                        let uu____1268 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1268 in
                      FStar_Util.Inl uu____1267 in
                    Some uu____1261 in
                  let ret_gtot_type =
                    let uu____1288 =
                      let uu____1294 =
                        let uu____1295 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1295 in
                      FStar_Util.Inl uu____1294 in
                    Some uu____1288 in
                  let mk_forall1 x body =
                    let uu____1315 =
                      let uu____1318 =
                        let uu____1319 =
                          let uu____1329 =
                            let uu____1331 =
                              let uu____1332 =
                                let uu____1333 =
                                  let uu____1337 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1337] in
                                FStar_Syntax_Util.abs uu____1333 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1332 in
                            [uu____1331] in
                          (FStar_Syntax_Util.tforall, uu____1329) in
                        FStar_Syntax_Syntax.Tm_app uu____1319 in
                      FStar_Syntax_Syntax.mk uu____1318 in
                    uu____1315 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1351 =
                      let uu____1352 = FStar_Syntax_Subst.compress t in
                      uu____1352.FStar_Syntax_Syntax.n in
                    match uu____1351 with
                    | FStar_Syntax_Syntax.Tm_type uu____1355 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1370  ->
                              match uu____1370 with
                              | (b,uu____1374) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1375 -> true in
                  let rec is_monotonic t =
                    let uu____1380 =
                      let uu____1381 = FStar_Syntax_Subst.compress t in
                      uu____1381.FStar_Syntax_Syntax.n in
                    match uu____1380 with
                    | FStar_Syntax_Syntax.Tm_type uu____1384 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1399  ->
                              match uu____1399 with
                              | (b,uu____1403) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1404 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1456 =
                      let uu____1457 = FStar_Syntax_Subst.compress t1 in
                      uu____1457.FStar_Syntax_Syntax.n in
                    match uu____1456 with
                    | FStar_Syntax_Syntax.Tm_type uu____1460 -> rel x y
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
                        let uu____1506 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1506
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1509 =
                              let uu____1512 =
                                let uu____1518 =
                                  let uu____1519 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1519 in
                                [uu____1518] in
                              FStar_Syntax_Util.mk_app x uu____1512 in
                            let uu____1520 =
                              let uu____1523 =
                                let uu____1529 =
                                  let uu____1530 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1530 in
                                [uu____1529] in
                              FStar_Syntax_Util.mk_app y uu____1523 in
                            mk_rel1 b uu____1509 uu____1520 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1535 =
                               let uu____1536 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1539 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1536 uu____1539 in
                             let uu____1542 =
                               let uu____1543 =
                                 let uu____1546 =
                                   let uu____1552 =
                                     let uu____1553 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1553 in
                                   [uu____1552] in
                                 FStar_Syntax_Util.mk_app x uu____1546 in
                               let uu____1554 =
                                 let uu____1557 =
                                   let uu____1563 =
                                     let uu____1564 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1564 in
                                   [uu____1563] in
                                 FStar_Syntax_Util.mk_app y uu____1557 in
                               mk_rel1 b uu____1543 uu____1554 in
                             FStar_Syntax_Util.mk_imp uu____1535 uu____1542 in
                           let uu____1565 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1565)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___98_1586 = t1 in
                          let uu____1587 =
                            let uu____1588 =
                              let uu____1596 =
                                let uu____1597 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1597 in
                              ([binder], uu____1596) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1588 in
                          {
                            FStar_Syntax_Syntax.n = uu____1587;
                            FStar_Syntax_Syntax.tk =
                              (uu___98_1586.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___98_1586.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___98_1586.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1609 ->
                        failwith "unhandled arrow"
                    | uu____1617 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1632 =
                        let uu____1633 = FStar_Syntax_Subst.compress t1 in
                        uu____1633.FStar_Syntax_Syntax.n in
                      match uu____1632 with
                      | FStar_Syntax_Syntax.Tm_type uu____1636 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1653 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1653
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1668 =
                                let uu____1669 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1669 i in
                              FStar_Syntax_Syntax.fvar uu____1668
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1690 =
                            let uu____1694 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1699  ->
                                     match uu____1699 with
                                     | (t2,q) ->
                                         let uu____1704 = project i x in
                                         let uu____1705 = project i y in
                                         mk_stronger t2 uu____1704 uu____1705)
                                args in
                            match uu____1694 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1690 with
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
                                 fun uu____1761  ->
                                   match uu____1761 with
                                   | (bv,q) ->
                                       let uu____1766 =
                                         let uu____1767 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1767 in
                                       FStar_Syntax_Syntax.gen_bv uu____1766
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1771 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1771) bvs in
                          let body =
                            let uu____1773 = FStar_Syntax_Util.mk_app x args in
                            let uu____1774 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1773 uu____1774 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1777 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1779 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1780 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1781 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1779 uu____1780 uu____1781 in
                    let uu____1782 =
                      let uu____1786 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1786 in
                    FStar_Syntax_Util.abs uu____1782 body ret_tot_type in
                  let stronger1 =
                    let uu____1801 = mk_lid "stronger" in
                    register env1 uu____1801 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1807 = FStar_Util.prefix gamma in
                    match uu____1807 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (Prims.fst post).FStar_Syntax_Syntax.sort in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1833 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1833 in
                          let uu____1836 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1836 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1844 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1844 in
                              let guard_free1 =
                                let uu____1851 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1851 in
                              let pat =
                                let uu____1855 =
                                  let uu____1861 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1861] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1855 in
                              let pattern_guarded_body =
                                let uu____1865 =
                                  let uu____1866 =
                                    let uu____1871 =
                                      let uu____1872 =
                                        let uu____1879 =
                                          let uu____1881 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1881] in
                                        [uu____1879] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1872 in
                                    (body, uu____1871) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1866 in
                                mk1 uu____1865 in
                              FStar_Syntax_Util.close_forall binders1
                                pattern_guarded_body
                          | uu____1884 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1887 =
                            let uu____1888 =
                              let uu____1889 =
                                let uu____1890 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1893 =
                                  let uu____1899 = args_of_binders1 wp_args in
                                  let uu____1901 =
                                    let uu____1903 =
                                      let uu____1904 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1904 in
                                    [uu____1903] in
                                  FStar_List.append uu____1899 uu____1901 in
                                FStar_Syntax_Util.mk_app uu____1890
                                  uu____1893 in
                              FStar_Syntax_Util.mk_imp equiv uu____1889 in
                            FStar_Syntax_Util.mk_forall k uu____1888 in
                          FStar_Syntax_Util.abs gamma uu____1887
                            ret_gtot_type in
                        let uu____1905 =
                          let uu____1909 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1909 in
                        FStar_Syntax_Util.abs uu____1905 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1916 = mk_lid "wp_ite" in
                    register env1 uu____1916 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1922 = FStar_Util.prefix gamma in
                    match uu____1922 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1946 =
                            let uu____1947 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (Prims.fst post) in
                            let uu____1950 =
                              let uu____1956 =
                                let uu____1957 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1957 in
                              [uu____1956] in
                            FStar_Syntax_Util.mk_app uu____1947 uu____1950 in
                          FStar_Syntax_Util.mk_forall x uu____1946 in
                        let uu____1958 =
                          let uu____1962 =
                            let uu____1966 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1966 gamma in
                          FStar_List.append binders uu____1962 in
                        FStar_Syntax_Util.abs uu____1958 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1975 = mk_lid "null_wp" in
                    register env1 uu____1975 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____1984 =
                        let uu____1990 =
                          let uu____1992 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____1993 =
                            let uu____1995 =
                              let uu____1998 =
                                let uu____2004 =
                                  let uu____2005 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2005 in
                                [uu____2004] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1998 in
                            let uu____2006 =
                              let uu____2010 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2010] in
                            uu____1995 :: uu____2006 in
                          uu____1992 :: uu____1993 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1990 in
                      FStar_Syntax_Util.mk_app stronger2 uu____1984 in
                    let uu____2013 =
                      let uu____2017 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2017 in
                    FStar_Syntax_Util.abs uu____2013 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2024 = mk_lid "wp_trivial" in
                    register env1 uu____2024 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2029 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2029
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2034 =
                      let uu____2036 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2036 in
                    let uu____2041 =
                      let uu___99_2042 = ed in
                      let uu____2043 =
                        let uu____2044 = c wp_if_then_else2 in
                        ([], uu____2044) in
                      let uu____2046 =
                        let uu____2047 = c wp_ite2 in ([], uu____2047) in
                      let uu____2049 =
                        let uu____2050 = c stronger2 in ([], uu____2050) in
                      let uu____2052 =
                        let uu____2053 = c wp_close2 in ([], uu____2053) in
                      let uu____2055 =
                        let uu____2056 = c wp_assert2 in ([], uu____2056) in
                      let uu____2058 =
                        let uu____2059 = c wp_assume2 in ([], uu____2059) in
                      let uu____2061 =
                        let uu____2062 = c null_wp2 in ([], uu____2062) in
                      let uu____2064 =
                        let uu____2065 = c wp_trivial2 in ([], uu____2065) in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___99_2042.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___99_2042.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___99_2042.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___99_2042.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___99_2042.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___99_2042.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___99_2042.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___99_2042.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2043;
                        FStar_Syntax_Syntax.ite_wp = uu____2046;
                        FStar_Syntax_Syntax.stronger = uu____2049;
                        FStar_Syntax_Syntax.close_wp = uu____2052;
                        FStar_Syntax_Syntax.assert_p = uu____2055;
                        FStar_Syntax_Syntax.assume_p = uu____2058;
                        FStar_Syntax_Syntax.null_wp = uu____2061;
                        FStar_Syntax_Syntax.trivial = uu____2064;
                        FStar_Syntax_Syntax.repr =
                          (uu___99_2042.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___99_2042.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___99_2042.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___99_2042.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2034, uu____2041)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2081 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2093 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___86_2103  ->
    match uu___86_2103 with
    | FStar_Syntax_Syntax.Total (t,uu____2105) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___85_2114  ->
                match uu___85_2114 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2115 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2117 =
          let uu____2118 =
            let uu____2119 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2119 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2118 in
        failwith uu____2117
    | FStar_Syntax_Syntax.GTotal uu____2120 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___87_2128  ->
    match uu___87_2128 with
    | N t ->
        let uu____2130 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2130
    | M t ->
        let uu____2132 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2132
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2136,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2138;
                      FStar_Syntax_Syntax.pos = uu____2139;
                      FStar_Syntax_Syntax.vars = uu____2140;_})
        -> nm_of_comp n2
    | uu____2151 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2163 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2163 with | M uu____2164 -> true | N uu____2165 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2169 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2179 =
        let uu____2183 =
          let uu____2184 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2184 in
        [uu____2183] in
      let uu____2185 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2179 uu____2185 in
    let uu____2188 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2188
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
          (let uu____2223 =
             let uu____2231 =
               let uu____2235 =
                 let uu____2238 =
                   let uu____2239 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2239 in
                 let uu____2240 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2238, uu____2240) in
               [uu____2235] in
             let uu____2245 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2231, uu____2245) in
           FStar_Syntax_Syntax.Tm_arrow uu____2223)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2278) ->
          let binders1 =
            FStar_List.map
              (fun uu____2297  ->
                 match uu____2297 with
                 | (bv,aqual) ->
                     let uu____2304 =
                       let uu___100_2305 = bv in
                       let uu____2306 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___100_2305.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___100_2305.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2306
                       } in
                     (uu____2304, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2309,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2311);
                             FStar_Syntax_Syntax.tk = uu____2312;
                             FStar_Syntax_Syntax.pos = uu____2313;
                             FStar_Syntax_Syntax.vars = uu____2314;_})
               ->
               let uu____2331 =
                 let uu____2332 =
                   let uu____2340 =
                     let uu____2341 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2341 in
                   (binders1, uu____2340) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2332 in
               mk1 uu____2331
           | uu____2345 ->
               let uu____2346 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2346 with
                | N hn ->
                    let uu____2348 =
                      let uu____2349 =
                        let uu____2357 =
                          let uu____2358 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2358 in
                        (binders1, uu____2357) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2349 in
                    mk1 uu____2348
                | M a ->
                    let uu____2363 =
                      let uu____2364 =
                        let uu____2372 =
                          let uu____2376 =
                            let uu____2380 =
                              let uu____2383 =
                                let uu____2384 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2384 in
                              let uu____2385 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2383, uu____2385) in
                            [uu____2380] in
                          FStar_List.append binders1 uu____2376 in
                        let uu____2392 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2372, uu____2392) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2364 in
                    mk1 uu____2363))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2443 = f x in
                    FStar_Util.string_builder_append strb uu____2443);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2447 = f x1 in
                         FStar_Util.string_builder_append strb uu____2447))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2449 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2450 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2449 uu____2450 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2458 =
              let uu____2459 = FStar_Syntax_Subst.compress ty in
              uu____2459.FStar_Syntax_Syntax.n in
            match uu____2458 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2474 =
                  let uu____2475 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2475 in
                if uu____2474
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2489 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2489 s in
                       let uu____2491 =
                         let uu____2492 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2492 in
                       if uu____2491
                       then (debug1 ty1 sinter; Prims.raise Not_found)
                       else () in
                     let uu____2495 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2495 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2506  ->
                                  match uu____2506 with
                                  | (bv,uu____2512) ->
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
            | uu____2525 ->
                ((let uu____2527 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2527);
                 false) in
          let rec is_valid_application head2 =
            let uu____2532 =
              let uu____2533 = FStar_Syntax_Subst.compress head2 in
              uu____2533.FStar_Syntax_Syntax.n in
            match uu____2532 with
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
                  (let uu____2537 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2537)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2550 -> true
                 | uu____2560 ->
                     ((let uu____2562 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2562);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
                true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2566) ->
                is_valid_application t2
            | uu____2571 -> false in
          let uu____2572 = is_valid_application head1 in
          if uu____2572
          then
            let uu____2573 =
              let uu____2574 =
                let uu____2584 =
                  FStar_List.map
                    (fun uu____2594  ->
                       match uu____2594 with
                       | (t2,qual) ->
                           let uu____2607 = star_type' env t2 in
                           (uu____2607, qual)) args in
                (head1, uu____2584) in
              FStar_Syntax_Syntax.Tm_app uu____2574 in
            mk1 uu____2573
          else
            (let uu____2614 =
               let uu____2615 =
                 let uu____2616 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2616 in
               FStar_Errors.Err uu____2615 in
             Prims.raise uu____2614)
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_name _
         |FStar_Syntax_Syntax.Tm_type _|FStar_Syntax_Syntax.Tm_fvar _ -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2646 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2646 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___103_2652 = env in
                 let uu____2653 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2653;
                   subst = (uu___103_2652.subst);
                   tc_const = (uu___103_2652.tc_const)
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
               ((let uu___104_2670 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___104_2670.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___104_2670.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2677 =
            let uu____2678 =
              let uu____2683 = star_type' env t2 in (uu____2683, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2678 in
          mk1 uu____2677
      | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t2,something) ->
          let uu____2705 =
            let uu____2706 =
              let uu____2719 = star_type' env e in
              let uu____2720 =
                let uu____2725 = star_type' env t2 in
                FStar_Util.Inl uu____2725 in
              (uu____2719, uu____2720, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2706 in
          mk1 uu____2705
      | FStar_Syntax_Syntax.Tm_ascribed uu____2733 ->
          let uu____2746 =
            let uu____2747 =
              let uu____2748 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2748 in
            FStar_Errors.Err uu____2747 in
          Prims.raise uu____2746
      | FStar_Syntax_Syntax.Tm_refine uu____2749 ->
          let uu____2754 =
            let uu____2755 =
              let uu____2756 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2756 in
            FStar_Errors.Err uu____2755 in
          Prims.raise uu____2754
      | FStar_Syntax_Syntax.Tm_uinst uu____2757 ->
          let uu____2762 =
            let uu____2763 =
              let uu____2764 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2764 in
            FStar_Errors.Err uu____2763 in
          Prims.raise uu____2762
      | FStar_Syntax_Syntax.Tm_constant uu____2765 ->
          let uu____2766 =
            let uu____2767 =
              let uu____2768 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2768 in
            FStar_Errors.Err uu____2767 in
          Prims.raise uu____2766
      | FStar_Syntax_Syntax.Tm_match uu____2769 ->
          let uu____2785 =
            let uu____2786 =
              let uu____2787 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2787 in
            FStar_Errors.Err uu____2786 in
          Prims.raise uu____2785
      | FStar_Syntax_Syntax.Tm_let uu____2788 ->
          let uu____2796 =
            let uu____2797 =
              let uu____2798 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2798 in
            FStar_Errors.Err uu____2797 in
          Prims.raise uu____2796
      | FStar_Syntax_Syntax.Tm_uvar uu____2799 ->
          let uu____2808 =
            let uu____2809 =
              let uu____2810 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2810 in
            FStar_Errors.Err uu____2809 in
          Prims.raise uu____2808
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2811 =
            let uu____2812 =
              let uu____2813 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2813 in
            FStar_Errors.Err uu____2812 in
          Prims.raise uu____2811
      | FStar_Syntax_Syntax.Tm_delayed uu____2814 -> failwith "impossible"
let is_monadic uu___89_2847 =
  match uu___89_2847 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
    { FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _;
      FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _;_})
    |Some (FStar_Util.Inr (_,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___88_2884  ->
              match uu___88_2884 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____2885 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2889 =
      let uu____2890 = FStar_Syntax_Subst.compress t in
      uu____2890.FStar_Syntax_Syntax.n in
    match uu____2889 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2910 =
            let uu____2911 = FStar_List.hd args in Prims.fst uu____2911 in
          is_C uu____2910 in
        if r
        then
          ((let uu____2923 =
              let uu____2924 =
                FStar_List.for_all
                  (fun uu____2927  ->
                     match uu____2927 with | (h,uu____2931) -> is_C h) args in
              Prims.op_Negation uu____2924 in
            if uu____2923 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2935 =
              let uu____2936 =
                FStar_List.for_all
                  (fun uu____2939  ->
                     match uu____2939 with
                     | (h,uu____2943) ->
                         let uu____2944 = is_C h in
                         Prims.op_Negation uu____2944) args in
              Prims.op_Negation uu____2936 in
            if uu____2935 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2958 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____2958 with
         | M t1 ->
             ((let uu____2961 = is_C t1 in
               if uu____2961 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,_)
      |FStar_Syntax_Syntax.Tm_uinst (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
       (t1,_,_) -> is_C t1
    | uu____2988 -> false
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
          let uu____3019 =
            let uu____3020 =
              let uu____3030 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3031 =
                let uu____3035 =
                  let uu____3038 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3038) in
                [uu____3035] in
              (uu____3030, uu____3031) in
            FStar_Syntax_Syntax.Tm_app uu____3020 in
          mk1 uu____3019 in
        let uu____3046 =
          let uu____3050 = FStar_Syntax_Syntax.mk_binder p in [uu____3050] in
        let uu____3051 =
          let uu____3058 =
            let uu____3064 =
              let uu____3065 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3065 in
            FStar_Util.Inl uu____3064 in
          Some uu____3058 in
        FStar_Syntax_Util.abs uu____3046 body uu____3051
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___90_3078  ->
    match uu___90_3078 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3079 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos in
        let return_if uu____3223 =
          match uu____3223 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3244 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3245 =
                       let uu____3246 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3246 in
                     Prims.op_Negation uu____3245) in
                if uu____3244
                then
                  let uu____3247 =
                    let uu____3248 =
                      let uu____3249 = FStar_Syntax_Print.term_to_string e in
                      let uu____3250 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3251 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3249 uu____3250 uu____3251 in
                    FStar_Errors.Err uu____3248 in
                  Prims.raise uu____3247
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2)|(M t1,M t2) ->
                   (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3262 = mk_return env t1 s_e in
                     ((M t1), uu____3262, u_e)))
               | (M t1,N t2) ->
                   let uu____3265 =
                     let uu____3266 =
                       let uu____3267 = FStar_Syntax_Print.term_to_string e in
                       let uu____3268 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3269 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3267 uu____3268 uu____3269 in
                     FStar_Errors.Err uu____3266 in
                   Prims.raise uu____3265) in
        let ensure_m env1 e2 =
          let strip_m uu___91_3295 =
            match uu___91_3295 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3305 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3316 =
                let uu____3317 =
                  let uu____3320 =
                    let uu____3321 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3321 in
                  (uu____3320, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3317 in
              Prims.raise uu____3316
          | M uu____3325 ->
              let uu____3326 = check env1 e2 context_nm in strip_m uu____3326 in
        let uu____3330 =
          let uu____3331 = FStar_Syntax_Subst.compress e in
          uu____3331.FStar_Syntax_Syntax.n in
        match uu____3330 with
        | FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_name _
           |FStar_Syntax_Syntax.Tm_fvar _
            |FStar_Syntax_Syntax.Tm_abs _
             |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_app _
            -> let uu____3343 = infer env e in return_if uu____3343
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
        | FStar_Syntax_Syntax.Tm_let uu____3413 ->
            let uu____3421 =
              let uu____3422 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3422 in
            failwith uu____3421
        | FStar_Syntax_Syntax.Tm_type uu____3426 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3430 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3441 ->
            let uu____3446 =
              let uu____3447 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3447 in
            failwith uu____3446
        | FStar_Syntax_Syntax.Tm_uvar uu____3451 ->
            let uu____3460 =
              let uu____3461 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3461 in
            failwith uu____3460
        | FStar_Syntax_Syntax.Tm_delayed uu____3465 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3489 =
              let uu____3490 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3490 in
            failwith uu____3489
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
      let uu____3512 =
        let uu____3513 = FStar_Syntax_Subst.compress e in
        uu____3513.FStar_Syntax_Syntax.n in
      match uu____3512 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___105_3553 = env in
            let uu____3554 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3554;
              subst = (uu___105_3553.subst);
              tc_const = (uu___105_3553.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3563  ->
                 match uu____3563 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___106_3571 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_3571.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_3571.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3572 =
            FStar_List.fold_left
              (fun uu____3581  ->
                 fun uu____3582  ->
                   match (uu____3581, uu____3582) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3610 = is_C c in
                       if uu____3610
                       then
                         let xw =
                           let uu____3615 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "^w") None uu____3615 in
                         let x =
                           let uu___107_3617 = bv in
                           let uu____3618 =
                             let uu____3621 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3621 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___107_3617.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___107_3617.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3618
                           } in
                         let env3 =
                           let uu___108_3623 = env2 in
                           let uu____3624 =
                             let uu____3626 =
                               let uu____3627 =
                                 let uu____3632 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3632) in
                               FStar_Syntax_Syntax.NT uu____3627 in
                             uu____3626 :: (env2.subst) in
                           {
                             env = (uu___108_3623.env);
                             subst = uu____3624;
                             tc_const = (uu___108_3623.tc_const)
                           } in
                         let uu____3633 =
                           let uu____3635 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3636 =
                             let uu____3638 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3638 :: acc in
                           uu____3635 :: uu____3636 in
                         (env3, uu____3633)
                       else
                         (let x =
                            let uu___109_3642 = bv in
                            let uu____3643 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___109_3642.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___109_3642.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3643
                            } in
                          let uu____3646 =
                            let uu____3648 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3648 :: acc in
                          (env2, uu____3646))) (env1, []) binders1 in
          (match uu____3572 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3660 =
                 let check_what =
                   let uu____3672 = is_monadic what in
                   if uu____3672 then check_m else check_n in
                 let uu____3681 = check_what env2 body1 in
                 match uu____3681 with
                 | (t,s_body,u_body) ->
                     let uu____3691 =
                       let uu____3692 =
                         let uu____3693 = is_monadic what in
                         if uu____3693 then M t else N t in
                       comp_of_nm uu____3692 in
                     (uu____3691, s_body, u_body) in
               (match uu____3660 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3736 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___92_3738  ->
                                    match uu___92_3738 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3739 -> false)) in
                          if uu____3736
                          then
                            let double_starred_comp =
                              let uu____3747 =
                                let uu____3748 =
                                  let uu____3749 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____3749 in
                                FStar_All.pipe_left double_star uu____3748 in
                              FStar_Syntax_Syntax.mk_Total uu____3747 in
                            let flags =
                              FStar_List.filter
                                (fun uu___93_3754  ->
                                   match uu___93_3754 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3755 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____3756 =
                              let uu____3762 =
                                let uu____3763 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____3763 in
                              FStar_Util.Inl uu____3762 in
                            Some uu____3756
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___110_3783 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___110_3783.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___110_3783.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___110_3783.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____3784  ->
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
                          let uu____3801 =
                            let uu____3807 =
                              let uu____3811 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___94_3813  ->
                                        match uu___94_3813 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____3814 -> false)) in
                              if uu____3811
                              then
                                let uu____3818 =
                                  FStar_List.filter
                                    (fun uu___95_3820  ->
                                       match uu___95_3820 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____3821 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____3818)
                              else (lid, flags) in
                            FStar_Util.Inr uu____3807 in
                          Some uu____3801 in
                    let uu____3833 =
                      let comp1 =
                        let uu____3845 = is_monadic what in
                        let uu____3846 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3845 uu____3846 in
                      let uu____3847 =
                        FStar_Syntax_Util.ascribe u_body
                          (FStar_Util.Inr comp1) in
                      (uu____3847,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____3833 with
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
                FStar_Syntax_Syntax.ty = uu____3916;
                FStar_Syntax_Syntax.p = uu____3917;_};
            FStar_Syntax_Syntax.fv_delta = uu____3918;
            FStar_Syntax_Syntax.fv_qual = uu____3919;_}
          ->
          let uu____3925 =
            let uu____3928 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left Prims.fst uu____3928 in
          (match uu____3925 with
           | (uu____3944,t) ->
               let uu____3946 = let uu____3947 = normalize1 t in N uu____3947 in
               (uu____3946, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3964 = check_n env head1 in
          (match uu____3964 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3978 =
                   let uu____3979 = FStar_Syntax_Subst.compress t in
                   uu____3979.FStar_Syntax_Syntax.n in
                 match uu____3978 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3982 -> true
                 | uu____3990 -> false in
               let rec flatten1 t =
                 let uu____4002 =
                   let uu____4003 = FStar_Syntax_Subst.compress t in
                   uu____4003.FStar_Syntax_Syntax.n in
                 match uu____4002 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4015);
                                FStar_Syntax_Syntax.tk = uu____4016;
                                FStar_Syntax_Syntax.pos = uu____4017;
                                FStar_Syntax_Syntax.vars = uu____4018;_})
                     when is_arrow t1 ->
                     let uu____4035 = flatten1 t1 in
                     (match uu____4035 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4087,uu____4088)
                     -> flatten1 e1
                 | uu____4107 ->
                     let uu____4108 =
                       let uu____4109 =
                         let uu____4110 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4110 in
                       FStar_Errors.Err uu____4109 in
                     Prims.raise uu____4108 in
               let uu____4118 = flatten1 t_head in
               (match uu____4118 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4163 =
                          let uu____4164 =
                            let uu____4165 = FStar_Util.string_of_int n1 in
                            let uu____4169 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4175 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4165 uu____4169 uu____4175 in
                          FStar_Errors.Err uu____4164 in
                        Prims.raise uu____4163)
                     else ();
                     (let uu____4180 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4180 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4207 args1 =
                            match uu____4207 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4250 =
                                       let uu____4251 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4251.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4250
                                 | (binders3,[]) ->
                                     let uu____4270 =
                                       let uu____4271 =
                                         let uu____4274 =
                                           let uu____4275 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4275 in
                                         FStar_Syntax_Subst.compress
                                           uu____4274 in
                                       uu____4271.FStar_Syntax_Syntax.n in
                                     (match uu____4270 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4291 =
                                            let uu____4292 =
                                              let uu____4293 =
                                                let uu____4301 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4301) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4293 in
                                            mk1 uu____4292 in
                                          N uu____4291
                                      | uu____4305 -> failwith "wat?")
                                 | ([],uu____4306::uu____4307) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4332)::binders3,(arg,uu____4335)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4369 = FStar_List.splitAt n' binders1 in
                          (match uu____4369 with
                           | (binders2,uu____4386) ->
                               let uu____4399 =
                                 let uu____4409 =
                                   FStar_List.map2
                                     (fun uu____4429  ->
                                        fun uu____4430  ->
                                          match (uu____4429, uu____4430) with
                                          | ((bv,uu____4447),(arg,q)) ->
                                              let uu____4454 =
                                                let uu____4455 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4455.FStar_Syntax_Syntax.n in
                                              (match uu____4454 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4465 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4478 ->
                                                   let uu____4479 =
                                                     check_n env arg in
                                                   (match uu____4479 with
                                                    | (uu____4490,s_arg,u_arg)
                                                        ->
                                                        let uu____4493 =
                                                          let uu____4497 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4497
                                                          then
                                                            let uu____4501 =
                                                              let uu____4504
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4504, q) in
                                                            [uu____4501;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4493))))
                                     binders2 args in
                                 FStar_List.split uu____4409 in
                               (match uu____4399 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4551 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4557 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4551, uu____4557)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,_)
        |FStar_Syntax_Syntax.Tm_meta (e1,_)|FStar_Syntax_Syntax.Tm_ascribed
         (e1,_,_) -> infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4630 = let uu____4631 = env.tc_const c in N uu____4631 in
          (uu____4630, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4632 ->
          let uu____4640 =
            let uu____4641 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4641 in
          failwith uu____4640
      | FStar_Syntax_Syntax.Tm_type uu____4645 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4649 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4660 ->
          let uu____4665 =
            let uu____4666 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4666 in
          failwith uu____4665
      | FStar_Syntax_Syntax.Tm_uvar uu____4670 ->
          let uu____4679 =
            let uu____4680 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4680 in
          failwith uu____4679
      | FStar_Syntax_Syntax.Tm_delayed uu____4684 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4708 =
            let uu____4709 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4709 in
          failwith uu____4708
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
          let uu____4747 = check_n env e0 in
          match uu____4747 with
          | (uu____4754,s_e0,u_e0) ->
              let uu____4757 =
                let uu____4775 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4808 = FStar_Syntax_Subst.open_branch b in
                       match uu____4808 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___111_4840 = env in
                             let uu____4841 =
                               let uu____4842 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4842 in
                             {
                               env = uu____4841;
                               subst = (uu___111_4840.subst);
                               tc_const = (uu___111_4840.tc_const)
                             } in
                           let uu____4844 = f env1 body in
                           (match uu____4844 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4893 ->
                           Prims.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4775 in
              (match uu____4757 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____4958 = FStar_List.hd nms in
                     match uu____4958 with | M t1|N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___96_4961  ->
                          match uu___96_4961 with
                          | M uu____4962 -> true
                          | uu____4963 -> false) nms in
                   let uu____4964 =
                     let uu____4987 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5039  ->
                              match uu____5039 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false )|(M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5135 =
                                         check env original_body (M t2) in
                                       (match uu____5135 with
                                        | (uu____5158,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5187,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____4987 in
                   (match uu____4964 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5306  ->
                                 match uu____5306 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5347 =
                                         let uu____5348 =
                                           let uu____5358 =
                                             let uu____5362 =
                                               let uu____5365 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5366 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5365, uu____5366) in
                                             [uu____5362] in
                                           (s_body, uu____5358) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5348 in
                                       mk1 uu____5347 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5388 =
                              let uu____5392 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5392] in
                            let uu____5393 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5395 =
                              let uu____5402 =
                                let uu____5408 =
                                  let uu____5409 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5409 in
                                FStar_Util.Inl uu____5408 in
                              Some uu____5402 in
                            FStar_Syntax_Util.abs uu____5388 uu____5393
                              uu____5395 in
                          let t1_star =
                            let uu____5423 =
                              let uu____5427 =
                                let uu____5428 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5428 in
                              [uu____5427] in
                            let uu____5429 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5423 uu____5429 in
                          let uu____5432 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, (FStar_Util.Inl t1_star), None)) in
                          let uu____5446 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5432, uu____5446)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5460 =
                             let uu____5463 =
                               let uu____5464 =
                                 let uu____5477 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5477, (FStar_Util.Inl t1_star), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5464 in
                             mk1 uu____5463 in
                           let uu____5490 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5460, uu____5490))))
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
              let uu____5533 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5533] in
            let uu____5534 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5534 with
            | (x_binders1,e21) ->
                let uu____5542 = infer env e1 in
                (match uu____5542 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5553 = is_C t1 in
                       if uu____5553
                       then
                         let uu___112_5554 = binding in
                         let uu____5555 =
                           let uu____5558 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5558 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___112_5554.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___112_5554.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5555;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___112_5554.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___112_5554.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___113_5561 = env in
                       let uu____5562 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___114_5563 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_5563.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_5563.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5562;
                         subst = (uu___113_5561.subst);
                         tc_const = (uu___113_5561.tc_const)
                       } in
                     let uu____5564 = proceed env1 e21 in
                     (match uu____5564 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___115_5575 = binding in
                            let uu____5576 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___115_5575.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___115_5575.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5576;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___115_5575.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___115_5575.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5579 =
                            let uu____5582 =
                              let uu____5583 =
                                let uu____5591 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___116_5596 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___116_5596.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___116_5596.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___116_5596.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___116_5596.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5591) in
                              FStar_Syntax_Syntax.Tm_let uu____5583 in
                            mk1 uu____5582 in
                          let uu____5597 =
                            let uu____5600 =
                              let uu____5601 =
                                let uu____5609 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___117_5614 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___117_5614.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___117_5614.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___117_5614.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___117_5614.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5609) in
                              FStar_Syntax_Syntax.Tm_let uu____5601 in
                            mk1 uu____5600 in
                          (nm_rec, uu____5579, uu____5597))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___118_5623 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___118_5623.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___118_5623.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___118_5623.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___119_5625 = env in
                       let uu____5626 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___120_5627 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___120_5627.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___120_5627.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5626;
                         subst = (uu___119_5625.subst);
                         tc_const = (uu___119_5625.tc_const)
                       } in
                     let uu____5628 = ensure_m env1 e21 in
                     (match uu____5628 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5645 =
                              let uu____5646 =
                                let uu____5656 =
                                  let uu____5660 =
                                    let uu____5663 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5664 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5663, uu____5664) in
                                  [uu____5660] in
                                (s_e2, uu____5656) in
                              FStar_Syntax_Syntax.Tm_app uu____5646 in
                            mk1 uu____5645 in
                          let s_e22 =
                            let uu____5673 =
                              let uu____5680 =
                                let uu____5686 =
                                  let uu____5687 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5687 in
                                FStar_Util.Inl uu____5686 in
                              Some uu____5680 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____5673 in
                          let body =
                            let uu____5701 =
                              let uu____5702 =
                                let uu____5712 =
                                  let uu____5716 =
                                    let uu____5719 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5719) in
                                  [uu____5716] in
                                (s_e1, uu____5712) in
                              FStar_Syntax_Syntax.Tm_app uu____5702 in
                            mk1 uu____5701 in
                          let uu____5727 =
                            let uu____5728 =
                              let uu____5732 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5732] in
                            let uu____5733 =
                              let uu____5740 =
                                let uu____5746 =
                                  let uu____5747 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5747 in
                                FStar_Util.Inl uu____5746 in
                              Some uu____5740 in
                            FStar_Syntax_Util.abs uu____5728 body uu____5733 in
                          let uu____5758 =
                            let uu____5761 =
                              let uu____5762 =
                                let uu____5770 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___121_5775 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5775.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5775.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5775.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5775.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5770) in
                              FStar_Syntax_Syntax.Tm_let uu____5762 in
                            mk1 uu____5761 in
                          ((M t2), uu____5727, uu____5758)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5784 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____5784 in
      let uu____5789 = check env e mn in
      match uu____5789 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5799 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5812 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____5812 in
      let uu____5817 = check env e mn in
      match uu____5817 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5827 -> failwith "[check_m]: impossible"
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
        (let uu____5849 =
           let uu____5850 = is_C c in Prims.op_Negation uu____5850 in
         if uu____5849 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____5862 =
           let uu____5863 = FStar_Syntax_Subst.compress c in
           uu____5863.FStar_Syntax_Syntax.n in
         match uu____5862 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5882 = FStar_Syntax_Util.head_and_args wp in
             (match uu____5882 with
              | (wp_head,wp_args) ->
                  ((let uu____5909 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5922 =
                           let uu____5923 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5923 in
                         Prims.op_Negation uu____5922) in
                    if uu____5909 then failwith "mismatch" else ());
                   (let uu____5932 =
                      let uu____5933 =
                        let uu____5943 =
                          FStar_List.map2
                            (fun uu____5953  ->
                               fun uu____5954  ->
                                 match (uu____5953, uu____5954) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____5977 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____5977
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____5980 = print_implicit q in
                                         let uu____5981 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____5980 uu____5981)
                                      else ();
                                      (let uu____5983 =
                                         trans_F_ env arg wp_arg in
                                       (uu____5983, q)))) args wp_args in
                        (head1, uu____5943) in
                      FStar_Syntax_Syntax.Tm_app uu____5933 in
                    mk1 uu____5932)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6005 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6005 with
              | (binders_orig,comp1) ->
                  let uu____6010 =
                    let uu____6018 =
                      FStar_List.map
                        (fun uu____6032  ->
                           match uu____6032 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6045 = is_C h in
                               if uu____6045
                               then
                                 let w' =
                                   let uu____6052 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "-w'") None uu____6052 in
                                 let uu____6053 =
                                   let uu____6057 =
                                     let uu____6061 =
                                       let uu____6064 =
                                         let uu____6065 =
                                           let uu____6066 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6066 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6065 in
                                       (uu____6064, q) in
                                     [uu____6061] in
                                   (w', q) :: uu____6057 in
                                 (w', uu____6053)
                               else
                                 (let x =
                                    let uu____6078 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "-x") None uu____6078 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6018 in
                  (match uu____6010 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6108 =
                           let uu____6110 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6110 in
                         FStar_Syntax_Subst.subst_comp uu____6108 comp1 in
                       let app =
                         let uu____6114 =
                           let uu____6115 =
                             let uu____6125 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6132 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6133 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6132, uu____6133)) bvs in
                             (wp, uu____6125) in
                           FStar_Syntax_Syntax.Tm_app uu____6115 in
                         mk1 uu____6114 in
                       let comp3 =
                         let uu____6138 = type_of_comp comp2 in
                         let uu____6139 = is_monadic_comp comp2 in
                         trans_G env uu____6138 uu____6139 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6141,uu____6142) ->
             trans_F_ env e wp
         | uu____6161 -> failwith "impossible trans_F_")
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
            let uu____6176 =
              let uu____6177 = star_type' env h in
              let uu____6180 =
                let uu____6186 =
                  let uu____6189 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6189) in
                [uu____6186] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6177;
                FStar_Syntax_Syntax.effect_args = uu____6180;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6176
          else
            (let uu____6195 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6195)
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
    fun t  -> let uu____6206 = n env.env t in star_type' env uu____6206
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6218 = n env.env t in check_n env uu____6218
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6228 = n env.env c in
        let uu____6229 = n env.env wp in trans_F_ env uu____6228 uu____6229