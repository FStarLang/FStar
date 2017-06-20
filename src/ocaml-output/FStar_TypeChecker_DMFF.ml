open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ;}
let __proj__Mkenv__item__env: env -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
let __proj__Mkenv__item__subst:
  env -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
let __proj__Mkenv__item__tc_const:
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
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
              let uu___102_94 = a in
              let uu____95 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___102_94.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___102_94.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____95
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____103 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____103
             then
               (d "Elaborating extra WP combinators";
                (let uu____105 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____105))
             else ());
            (let rec collect_binders t =
               let uu____114 =
                 let uu____115 =
                   let uu____118 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____118 in
                 uu____115.FStar_Syntax_Syntax.n in
               match uu____114 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____140) -> t1
                     | uu____147 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____150 = collect_binders rest in
                   FStar_List.append bs uu____150
               | FStar_Syntax_Syntax.Tm_type uu____156 -> []
               | uu____159 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____171 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____171 FStar_Syntax_Util.name_binders in
             (let uu____182 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____182
              then
                let uu____183 =
                  let uu____184 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____184 in
                d uu____183
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____216 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____216 with
                | (sigelt,fv) ->
                    ((let uu____222 =
                        let uu____224 = FStar_ST.read sigelts in sigelt ::
                          uu____224 in
                      FStar_ST.write sigelts uu____222);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____245  ->
                     match uu____245 with
                     | (t,b) ->
                         let uu____252 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____252)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____269 = FStar_Syntax_Syntax.as_implicit true in
                     ((fst t), uu____269)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____282 = FStar_Syntax_Syntax.bv_to_name (fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____282) in
              let uu____283 =
                let uu____295 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let body =
                      let uu____315 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____315 in
                    let uu____318 =
                      let uu____319 =
                        let uu____323 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____324 =
                          let uu____326 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____326] in
                        uu____323 :: uu____324 in
                      FStar_List.append binders uu____319 in
                    FStar_Syntax_Util.abs uu____318 body None in
                  let uu____329 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____330 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____329, uu____330) in
                match uu____295 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____361 =
                        let uu____362 =
                          let uu____372 =
                            let uu____376 =
                              FStar_List.map
                                (fun uu____384  ->
                                   match uu____384 with
                                   | (bv,uu____390) ->
                                       let uu____391 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____392 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____391, uu____392)) binders in
                            let uu____393 =
                              let uu____397 =
                                let uu____400 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____401 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____400, uu____401) in
                              let uu____402 =
                                let uu____406 =
                                  let uu____409 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____409) in
                                [uu____406] in
                              uu____397 :: uu____402 in
                            FStar_List.append uu____376 uu____393 in
                          (fv, uu____372) in
                        FStar_Syntax_Syntax.Tm_app uu____362 in
                      mk1 uu____361 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____283 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____455 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____455 in
                    let ret1 =
                      let uu____458 =
                        let uu____459 =
                          let uu____462 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____462 in
                        FStar_Syntax_Util.residual_tot uu____459 in
                      Some uu____458 in
                    let body =
                      let uu____464 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____464 ret1 in
                    let uu____465 =
                      let uu____466 = mk_all_implicit binders in
                      let uu____470 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____466 uu____470 in
                    FStar_Syntax_Util.abs uu____465 body ret1 in
                  let c_pure1 =
                    let uu____485 = mk_lid "pure" in
                    register env1 uu____485 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____490 =
                        let uu____491 =
                          let uu____492 =
                            let uu____496 =
                              let uu____497 =
                                let uu____498 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____498 in
                              FStar_Syntax_Syntax.mk_binder uu____497 in
                            [uu____496] in
                          let uu____499 =
                            let uu____502 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____502 in
                          FStar_Syntax_Util.arrow uu____492 uu____499 in
                        mk_gctx uu____491 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____490 in
                    let r =
                      let uu____504 =
                        let uu____505 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____505 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____504 in
                    let ret1 =
                      let uu____508 =
                        let uu____509 =
                          let uu____512 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____512 in
                        FStar_Syntax_Util.residual_tot uu____509 in
                      Some uu____508 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____519 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____522 =
                          let uu____528 =
                            let uu____530 =
                              let uu____531 =
                                let uu____532 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____532
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____531 in
                            [uu____530] in
                          FStar_List.append gamma_as_args uu____528 in
                        FStar_Syntax_Util.mk_app uu____519 uu____522 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____535 =
                      let uu____536 = mk_all_implicit binders in
                      let uu____540 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____536 uu____540 in
                    FStar_Syntax_Util.abs uu____535 outer_body ret1 in
                  let c_app1 =
                    let uu____559 = mk_lid "app" in
                    register env1 uu____559 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____566 =
                        let uu____570 =
                          let uu____571 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____571 in
                        [uu____570] in
                      let uu____572 =
                        let uu____575 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____575 in
                      FStar_Syntax_Util.arrow uu____566 uu____572 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____578 =
                        let uu____579 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____579 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____578 in
                    let ret1 =
                      let uu____582 =
                        let uu____583 =
                          let uu____586 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____586 in
                        FStar_Syntax_Util.residual_tot uu____583 in
                      Some uu____582 in
                    let uu____587 =
                      let uu____588 = mk_all_implicit binders in
                      let uu____592 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____588 uu____592 in
                    let uu____610 =
                      let uu____611 =
                        let uu____617 =
                          let uu____619 =
                            let uu____622 =
                              let uu____628 =
                                let uu____630 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____630] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____628 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____622 in
                          let uu____631 =
                            let uu____635 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____635] in
                          uu____619 :: uu____631 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____617 in
                      FStar_Syntax_Util.mk_app c_app1 uu____611 in
                    FStar_Syntax_Util.abs uu____587 uu____610 ret1 in
                  let c_lift11 =
                    let uu____639 = mk_lid "lift1" in
                    register env1 uu____639 c_lift1 in
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
                      let uu____647 =
                        let uu____651 =
                          let uu____652 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____652 in
                        let uu____653 =
                          let uu____655 =
                            let uu____656 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____656 in
                          [uu____655] in
                        uu____651 :: uu____653 in
                      let uu____657 =
                        let uu____660 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____660 in
                      FStar_Syntax_Util.arrow uu____647 uu____657 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____663 =
                        let uu____664 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____664 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____663 in
                    let a2 =
                      let uu____666 =
                        let uu____667 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____667 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____666 in
                    let ret1 =
                      let uu____670 =
                        let uu____671 =
                          let uu____674 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____674 in
                        FStar_Syntax_Util.residual_tot uu____671 in
                      Some uu____670 in
                    let uu____675 =
                      let uu____676 = mk_all_implicit binders in
                      let uu____680 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____676 uu____680 in
                    let uu____702 =
                      let uu____703 =
                        let uu____709 =
                          let uu____711 =
                            let uu____714 =
                              let uu____720 =
                                let uu____722 =
                                  let uu____725 =
                                    let uu____731 =
                                      let uu____733 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____733] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____731 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____725 in
                                let uu____734 =
                                  let uu____738 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____738] in
                                uu____722 :: uu____734 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____720 in
                            FStar_Syntax_Util.mk_app c_app1 uu____714 in
                          let uu____741 =
                            let uu____745 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____745] in
                          uu____711 :: uu____741 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____709 in
                      FStar_Syntax_Util.mk_app c_app1 uu____703 in
                    FStar_Syntax_Util.abs uu____675 uu____702 ret1 in
                  let c_lift21 =
                    let uu____749 = mk_lid "lift2" in
                    register env1 uu____749 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____756 =
                        let uu____760 =
                          let uu____761 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____761 in
                        [uu____760] in
                      let uu____762 =
                        let uu____765 =
                          let uu____766 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____766 in
                        FStar_Syntax_Syntax.mk_Total uu____765 in
                      FStar_Syntax_Util.arrow uu____756 uu____762 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____770 =
                        let uu____771 =
                          let uu____774 =
                            let uu____775 =
                              let uu____779 =
                                let uu____780 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____780 in
                              [uu____779] in
                            let uu____781 =
                              let uu____784 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____784 in
                            FStar_Syntax_Util.arrow uu____775 uu____781 in
                          mk_ctx uu____774 in
                        FStar_Syntax_Util.residual_tot uu____771 in
                      Some uu____770 in
                    let e1 =
                      let uu____786 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____786 in
                    let body =
                      let uu____788 =
                        let uu____789 =
                          let uu____793 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____793] in
                        FStar_List.append gamma uu____789 in
                      let uu____796 =
                        let uu____797 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____800 =
                          let uu____806 =
                            let uu____807 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____807 in
                          let uu____808 = args_of_binders1 gamma in uu____806
                            :: uu____808 in
                        FStar_Syntax_Util.mk_app uu____797 uu____800 in
                      FStar_Syntax_Util.abs uu____788 uu____796 ret1 in
                    let uu____810 =
                      let uu____811 = mk_all_implicit binders in
                      let uu____815 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____811 uu____815 in
                    FStar_Syntax_Util.abs uu____810 body ret1 in
                  let c_push1 =
                    let uu____832 = mk_lid "push" in
                    register env1 uu____832 c_push in
                  let ret_tot_wp_a =
                    Some (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____855 =
                        let uu____856 =
                          let uu____866 = args_of_binders1 binders in
                          (c, uu____866) in
                        FStar_Syntax_Syntax.Tm_app uu____856 in
                      mk1 uu____855
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____874 =
                        let uu____875 =
                          let uu____879 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____880 =
                            let uu____882 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____882] in
                          uu____879 :: uu____880 in
                        let uu____883 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____875 uu____883 in
                      FStar_Syntax_Syntax.mk_Total uu____874 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____887 =
                      let uu____888 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____888 in
                    let uu____894 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____896 =
                        let uu____899 =
                          let uu____905 =
                            let uu____907 =
                              let uu____910 =
                                let uu____916 =
                                  let uu____917 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____917 in
                                [uu____916] in
                              FStar_Syntax_Util.mk_app l_ite uu____910 in
                            [uu____907] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg uu____905 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____899 in
                      FStar_Syntax_Util.ascribe uu____896
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____887 uu____894
                      (Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____934 = mk_lid "wp_if_then_else" in
                    register env1 uu____934 wp_if_then_else in
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
                      let uu____945 =
                        let uu____951 =
                          let uu____953 =
                            let uu____956 =
                              let uu____962 =
                                let uu____964 =
                                  let uu____967 =
                                    let uu____973 =
                                      let uu____974 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____974 in
                                    [uu____973] in
                                  FStar_Syntax_Util.mk_app l_and uu____967 in
                                [uu____964] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____962 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____956 in
                          let uu____979 =
                            let uu____983 = FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____983] in
                          uu____953 :: uu____979 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____951 in
                      FStar_Syntax_Util.mk_app c_app1 uu____945 in
                    let uu____986 =
                      let uu____987 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____987 in
                    FStar_Syntax_Util.abs uu____986 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____994 = mk_lid "wp_assert" in
                    register env1 uu____994 wp_assert in
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
                      let uu____1005 =
                        let uu____1011 =
                          let uu____1013 =
                            let uu____1016 =
                              let uu____1022 =
                                let uu____1024 =
                                  let uu____1027 =
                                    let uu____1033 =
                                      let uu____1034 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1034 in
                                    [uu____1033] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1027 in
                                [uu____1024] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1022 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1016 in
                          let uu____1039 =
                            let uu____1043 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1043] in
                          uu____1013 :: uu____1039 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1011 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1005 in
                    let uu____1046 =
                      let uu____1047 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1047 in
                    FStar_Syntax_Util.abs uu____1046 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1054 = mk_lid "wp_assume" in
                    register env1 uu____1054 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1063 =
                        let uu____1067 =
                          let uu____1068 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1068 in
                        [uu____1067] in
                      let uu____1069 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1063 uu____1069 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1076 =
                        let uu____1082 =
                          let uu____1084 =
                            let uu____1087 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1087 in
                          let uu____1093 =
                            let uu____1097 =
                              let uu____1100 =
                                let uu____1106 =
                                  let uu____1108 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1108] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1106 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1100 in
                            [uu____1097] in
                          uu____1084 :: uu____1093 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1082 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1076 in
                    let uu____1115 =
                      let uu____1116 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1116 in
                    FStar_Syntax_Util.abs uu____1115 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1123 = mk_lid "wp_close" in
                    register env1 uu____1123 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1131 =
                      let uu____1132 =
                        let uu____1133 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1133 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1132 in
                    Some uu____1131 in
                  let mk_forall1 x body =
                    let uu____1145 =
                      let uu____1148 =
                        let uu____1149 =
                          let uu____1159 =
                            let uu____1161 =
                              let uu____1162 =
                                let uu____1163 =
                                  let uu____1164 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1164] in
                                FStar_Syntax_Util.abs uu____1163 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1162 in
                            [uu____1161] in
                          (FStar_Syntax_Util.tforall, uu____1159) in
                        FStar_Syntax_Syntax.Tm_app uu____1149 in
                      FStar_Syntax_Syntax.mk uu____1148 in
                    uu____1145 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1178 =
                      let uu____1179 = FStar_Syntax_Subst.compress t in
                      uu____1179.FStar_Syntax_Syntax.n in
                    match uu____1178 with
                    | FStar_Syntax_Syntax.Tm_type uu____1182 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1197  ->
                              match uu____1197 with
                              | (b,uu____1201) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1202 -> true in
                  let rec is_monotonic t =
                    let uu____1207 =
                      let uu____1208 = FStar_Syntax_Subst.compress t in
                      uu____1208.FStar_Syntax_Syntax.n in
                    match uu____1207 with
                    | FStar_Syntax_Syntax.Tm_type uu____1211 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1226  ->
                              match uu____1226 with
                              | (b,uu____1230) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1231 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1283 =
                      let uu____1284 = FStar_Syntax_Subst.compress t1 in
                      uu____1284.FStar_Syntax_Syntax.n in
                    match uu____1283 with
                    | FStar_Syntax_Syntax.Tm_type uu____1287 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1290);
                                      FStar_Syntax_Syntax.tk = uu____1291;
                                      FStar_Syntax_Syntax.pos = uu____1292;
                                      FStar_Syntax_Syntax.vars = uu____1293;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1316 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1316
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1319 =
                              let uu____1322 =
                                let uu____1328 =
                                  let uu____1329 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1329 in
                                [uu____1328] in
                              FStar_Syntax_Util.mk_app x uu____1322 in
                            let uu____1330 =
                              let uu____1333 =
                                let uu____1339 =
                                  let uu____1340 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1340 in
                                [uu____1339] in
                              FStar_Syntax_Util.mk_app y uu____1333 in
                            mk_rel1 b uu____1319 uu____1330 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1345 =
                               let uu____1346 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1349 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1346 uu____1349 in
                             let uu____1352 =
                               let uu____1353 =
                                 let uu____1356 =
                                   let uu____1362 =
                                     let uu____1363 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1363 in
                                   [uu____1362] in
                                 FStar_Syntax_Util.mk_app x uu____1356 in
                               let uu____1364 =
                                 let uu____1367 =
                                   let uu____1373 =
                                     let uu____1374 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1374 in
                                   [uu____1373] in
                                 FStar_Syntax_Util.mk_app y uu____1367 in
                               mk_rel1 b uu____1353 uu____1364 in
                             FStar_Syntax_Util.mk_imp uu____1345 uu____1352 in
                           let uu____1375 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1375)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1378);
                                      FStar_Syntax_Syntax.tk = uu____1379;
                                      FStar_Syntax_Syntax.pos = uu____1380;
                                      FStar_Syntax_Syntax.vars = uu____1381;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1404 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1404
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1407 =
                              let uu____1410 =
                                let uu____1416 =
                                  let uu____1417 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1417 in
                                [uu____1416] in
                              FStar_Syntax_Util.mk_app x uu____1410 in
                            let uu____1418 =
                              let uu____1421 =
                                let uu____1427 =
                                  let uu____1428 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1428 in
                                [uu____1427] in
                              FStar_Syntax_Util.mk_app y uu____1421 in
                            mk_rel1 b uu____1407 uu____1418 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1433 =
                               let uu____1434 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1437 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1434 uu____1437 in
                             let uu____1440 =
                               let uu____1441 =
                                 let uu____1444 =
                                   let uu____1450 =
                                     let uu____1451 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1451 in
                                   [uu____1450] in
                                 FStar_Syntax_Util.mk_app x uu____1444 in
                               let uu____1452 =
                                 let uu____1455 =
                                   let uu____1461 =
                                     let uu____1462 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1462 in
                                   [uu____1461] in
                                 FStar_Syntax_Util.mk_app y uu____1455 in
                               mk_rel1 b uu____1441 uu____1452 in
                             FStar_Syntax_Util.mk_imp uu____1433 uu____1440 in
                           let uu____1463 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1463)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___103_1484 = t1 in
                          let uu____1485 =
                            let uu____1486 =
                              let uu____1494 =
                                let uu____1495 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1495 in
                              ([binder], uu____1494) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1486 in
                          {
                            FStar_Syntax_Syntax.n = uu____1485;
                            FStar_Syntax_Syntax.tk =
                              (uu___103_1484.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___103_1484.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___103_1484.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1507 ->
                        failwith "unhandled arrow"
                    | uu____1515 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1530 =
                        let uu____1531 = FStar_Syntax_Subst.compress t1 in
                        uu____1531.FStar_Syntax_Syntax.n in
                      match uu____1530 with
                      | FStar_Syntax_Syntax.Tm_type uu____1534 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1551 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1551
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1566 =
                                let uu____1567 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1567 i in
                              FStar_Syntax_Syntax.fvar uu____1566
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1591 =
                            let uu____1595 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1600  ->
                                     match uu____1600 with
                                     | (t2,q) ->
                                         let uu____1605 = project i x in
                                         let uu____1606 = project i y in
                                         mk_stronger t2 uu____1605 uu____1606)
                                args in
                            match uu____1595 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1591 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1623);
                                      FStar_Syntax_Syntax.tk = uu____1624;
                                      FStar_Syntax_Syntax.pos = uu____1625;
                                      FStar_Syntax_Syntax.vars = uu____1626;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1648  ->
                                   match uu____1648 with
                                   | (bv,q) ->
                                       let uu____1653 =
                                         let uu____1654 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1654 in
                                       FStar_Syntax_Syntax.gen_bv uu____1653
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1658 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1658) bvs in
                          let body =
                            let uu____1660 = FStar_Syntax_Util.mk_app x args in
                            let uu____1661 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1660 uu____1661 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1666);
                                      FStar_Syntax_Syntax.tk = uu____1667;
                                      FStar_Syntax_Syntax.pos = uu____1668;
                                      FStar_Syntax_Syntax.vars = uu____1669;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1691  ->
                                   match uu____1691 with
                                   | (bv,q) ->
                                       let uu____1696 =
                                         let uu____1697 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1697 in
                                       FStar_Syntax_Syntax.gen_bv uu____1696
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1701 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1701) bvs in
                          let body =
                            let uu____1703 = FStar_Syntax_Util.mk_app x args in
                            let uu____1704 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1703 uu____1704 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1707 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1709 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1710 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1711 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1709 uu____1710 uu____1711 in
                    let uu____1712 =
                      let uu____1713 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1713 in
                    FStar_Syntax_Util.abs uu____1712 body ret_tot_type in
                  let stronger1 =
                    let uu____1728 = mk_lid "stronger" in
                    register env1 uu____1728 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1734 = FStar_Util.prefix gamma in
                    match uu____1734 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1760 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1760 in
                          let uu____1763 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1763 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1771 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1771 in
                              let guard_free1 =
                                let uu____1778 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1778 in
                              let pat =
                                let uu____1782 =
                                  let uu____1788 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1788] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1782 in
                              let pattern_guarded_body =
                                let uu____1792 =
                                  let uu____1793 =
                                    let uu____1798 =
                                      let uu____1799 =
                                        let uu____1806 =
                                          let uu____1808 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1808] in
                                        [uu____1806] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1799 in
                                    (body, uu____1798) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1793 in
                                mk1 uu____1792 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1811 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1814 =
                            let uu____1815 =
                              let uu____1816 =
                                let uu____1817 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1820 =
                                  let uu____1826 = args_of_binders1 wp_args in
                                  let uu____1828 =
                                    let uu____1830 =
                                      let uu____1831 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1831 in
                                    [uu____1830] in
                                  FStar_List.append uu____1826 uu____1828 in
                                FStar_Syntax_Util.mk_app uu____1817
                                  uu____1820 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1816 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1815 in
                          FStar_Syntax_Util.abs gamma uu____1814
                            ret_gtot_type in
                        let uu____1832 =
                          let uu____1833 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1833 in
                        FStar_Syntax_Util.abs uu____1832 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1840 = mk_lid "wp_ite" in
                    register env1 uu____1840 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1846 = FStar_Util.prefix gamma in
                    match uu____1846 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1870 =
                            let uu____1871 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____1874 =
                              let uu____1880 =
                                let uu____1881 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1881 in
                              [uu____1880] in
                            FStar_Syntax_Util.mk_app uu____1871 uu____1874 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1870 in
                        let uu____1882 =
                          let uu____1883 =
                            let uu____1887 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1887 gamma in
                          FStar_List.append binders uu____1883 in
                        FStar_Syntax_Util.abs uu____1882 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1896 = mk_lid "null_wp" in
                    register env1 uu____1896 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____1905 =
                        let uu____1911 =
                          let uu____1913 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____1914 =
                            let uu____1916 =
                              let uu____1919 =
                                let uu____1925 =
                                  let uu____1926 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____1926 in
                                [uu____1925] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1919 in
                            let uu____1927 =
                              let uu____1931 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____1931] in
                            uu____1916 :: uu____1927 in
                          uu____1913 :: uu____1914 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1911 in
                      FStar_Syntax_Util.mk_app stronger2 uu____1905 in
                    let uu____1934 =
                      let uu____1935 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____1935 in
                    FStar_Syntax_Util.abs uu____1934 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____1942 = mk_lid "wp_trivial" in
                    register env1 uu____1942 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____1947 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____1947
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____1952 =
                      let uu____1954 = FStar_ST.read sigelts in
                      FStar_List.rev uu____1954 in
                    let uu____1959 =
                      let uu___104_1960 = ed in
                      let uu____1961 =
                        let uu____1962 = c wp_if_then_else2 in
                        ([], uu____1962) in
                      let uu____1964 =
                        let uu____1965 = c wp_ite2 in ([], uu____1965) in
                      let uu____1967 =
                        let uu____1968 = c stronger2 in ([], uu____1968) in
                      let uu____1970 =
                        let uu____1971 = c wp_close2 in ([], uu____1971) in
                      let uu____1973 =
                        let uu____1974 = c wp_assert2 in ([], uu____1974) in
                      let uu____1976 =
                        let uu____1977 = c wp_assume2 in ([], uu____1977) in
                      let uu____1979 =
                        let uu____1980 = c null_wp2 in ([], uu____1980) in
                      let uu____1982 =
                        let uu____1983 = c wp_trivial2 in ([], uu____1983) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___104_1960.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___104_1960.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___104_1960.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___104_1960.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___104_1960.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___104_1960.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___104_1960.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____1961;
                        FStar_Syntax_Syntax.ite_wp = uu____1964;
                        FStar_Syntax_Syntax.stronger = uu____1967;
                        FStar_Syntax_Syntax.close_wp = uu____1970;
                        FStar_Syntax_Syntax.assert_p = uu____1973;
                        FStar_Syntax_Syntax.assume_p = uu____1976;
                        FStar_Syntax_Syntax.null_wp = uu____1979;
                        FStar_Syntax_Syntax.trivial = uu____1982;
                        FStar_Syntax_Syntax.repr =
                          (uu___104_1960.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___104_1960.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___104_1960.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___104_1960.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____1952, uu____1959)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___105_1998 = dmff_env in
      {
        env = env';
        subst = (uu___105_1998.subst);
        tc_const = (uu___105_1998.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2012 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2026 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___91_2038  ->
    match uu___91_2038 with
    | FStar_Syntax_Syntax.Total (t,uu____2040) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___90_2049  ->
                match uu___90_2049 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2050 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2052 =
          let uu____2053 =
            let uu____2054 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2054 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2053 in
        failwith uu____2052
    | FStar_Syntax_Syntax.GTotal uu____2055 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___92_2064  ->
    match uu___92_2064 with
    | N t ->
        let uu____2066 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2066
    | M t ->
        let uu____2068 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2068
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2073,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2075;
                      FStar_Syntax_Syntax.pos = uu____2076;
                      FStar_Syntax_Syntax.vars = uu____2077;_})
        -> nm_of_comp n2
    | uu____2088 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2102 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2102 with | M uu____2103 -> true | N uu____2104 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2109 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2120 =
        let uu____2124 =
          let uu____2125 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2125 in
        [uu____2124] in
      let uu____2126 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2120 uu____2126 in
    let uu____2129 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2129
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
          (let uu____2164 =
             let uu____2172 =
               let uu____2176 =
                 let uu____2179 =
                   let uu____2180 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2180 in
                 let uu____2181 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2179, uu____2181) in
               [uu____2176] in
             let uu____2186 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2172, uu____2186) in
           FStar_Syntax_Syntax.Tm_arrow uu____2164)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2215) ->
          let binders1 =
            FStar_List.map
              (fun uu____2234  ->
                 match uu____2234 with
                 | (bv,aqual) ->
                     let uu____2241 =
                       let uu___106_2242 = bv in
                       let uu____2243 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_2242.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_2242.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2243
                       } in
                     (uu____2241, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2246,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2248);
                             FStar_Syntax_Syntax.tk = uu____2249;
                             FStar_Syntax_Syntax.pos = uu____2250;
                             FStar_Syntax_Syntax.vars = uu____2251;_})
               ->
               let uu____2268 =
                 let uu____2269 =
                   let uu____2277 =
                     let uu____2278 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2278 in
                   (binders1, uu____2277) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2269 in
               mk1 uu____2268
           | uu____2282 ->
               let uu____2283 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2283 with
                | N hn ->
                    let uu____2285 =
                      let uu____2286 =
                        let uu____2294 =
                          let uu____2295 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2295 in
                        (binders1, uu____2294) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2286 in
                    mk1 uu____2285
                | M a ->
                    let uu____2300 =
                      let uu____2301 =
                        let uu____2309 =
                          let uu____2313 =
                            let uu____2317 =
                              let uu____2320 =
                                let uu____2321 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2321 in
                              let uu____2322 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2320, uu____2322) in
                            [uu____2317] in
                          FStar_List.append binders1 uu____2313 in
                        let uu____2329 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2309, uu____2329) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2301 in
                    mk1 uu____2300))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2380 = f x in
                    FStar_Util.string_builder_append strb uu____2380);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2384 = f x1 in
                         FStar_Util.string_builder_append strb uu____2384))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2386 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2387 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2386 uu____2387 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2395 =
              let uu____2396 = FStar_Syntax_Subst.compress ty in
              uu____2396.FStar_Syntax_Syntax.n in
            match uu____2395 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2411 =
                  let uu____2412 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2412 in
                if uu____2411
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2426 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2426 s in
                       let uu____2428 =
                         let uu____2429 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2429 in
                       if uu____2428
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2432 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2432 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2443  ->
                                  match uu____2443 with
                                  | (bv,uu____2449) ->
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
            | uu____2464 ->
                ((let uu____2466 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2466);
                 false) in
          let rec is_valid_application head2 =
            let uu____2471 =
              let uu____2472 = FStar_Syntax_Subst.compress head2 in
              uu____2472.FStar_Syntax_Syntax.n in
            match uu____2471 with
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
                  (let uu____2476 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2476)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2491 -> true
                 | uu____2501 ->
                     ((let uu____2503 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2503);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2504 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2505 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2507) ->
                is_valid_application t2
            | uu____2512 -> false in
          let uu____2513 = is_valid_application head1 in
          if uu____2513
          then
            let uu____2514 =
              let uu____2515 =
                let uu____2525 =
                  FStar_List.map
                    (fun uu____2535  ->
                       match uu____2535 with
                       | (t2,qual) ->
                           let uu____2548 = star_type' env t2 in
                           (uu____2548, qual)) args in
                (head1, uu____2525) in
              FStar_Syntax_Syntax.Tm_app uu____2515 in
            mk1 uu____2514
          else
            (let uu____2555 =
               let uu____2556 =
                 let uu____2557 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2557 in
               FStar_Errors.Err uu____2556 in
             raise uu____2555)
      | FStar_Syntax_Syntax.Tm_bvar uu____2558 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2559 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2560 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2561 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2577 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2577 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___109_2583 = env in
                 let uu____2584 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2584;
                   subst = (uu___109_2583.subst);
                   tc_const = (uu___109_2583.tc_const)
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
               ((let uu___110_2601 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___110_2601.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___110_2601.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2608 =
            let uu____2609 =
              let uu____2614 = star_type' env t2 in (uu____2614, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2609 in
          mk1 uu____2608
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2652 =
            let uu____2653 =
              let uu____2671 = star_type' env e in
              let uu____2672 =
                let uu____2682 =
                  let uu____2687 = star_type' env t2 in
                  FStar_Util.Inl uu____2687 in
                (uu____2682, None) in
              (uu____2671, uu____2672, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2653 in
          mk1 uu____2652
      | FStar_Syntax_Syntax.Tm_ascribed uu____2709 ->
          let uu____2727 =
            let uu____2728 =
              let uu____2729 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2729 in
            FStar_Errors.Err uu____2728 in
          raise uu____2727
      | FStar_Syntax_Syntax.Tm_refine uu____2730 ->
          let uu____2735 =
            let uu____2736 =
              let uu____2737 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2737 in
            FStar_Errors.Err uu____2736 in
          raise uu____2735
      | FStar_Syntax_Syntax.Tm_uinst uu____2738 ->
          let uu____2743 =
            let uu____2744 =
              let uu____2745 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2745 in
            FStar_Errors.Err uu____2744 in
          raise uu____2743
      | FStar_Syntax_Syntax.Tm_constant uu____2746 ->
          let uu____2747 =
            let uu____2748 =
              let uu____2749 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2749 in
            FStar_Errors.Err uu____2748 in
          raise uu____2747
      | FStar_Syntax_Syntax.Tm_match uu____2750 ->
          let uu____2766 =
            let uu____2767 =
              let uu____2768 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2768 in
            FStar_Errors.Err uu____2767 in
          raise uu____2766
      | FStar_Syntax_Syntax.Tm_let uu____2769 ->
          let uu____2777 =
            let uu____2778 =
              let uu____2779 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2779 in
            FStar_Errors.Err uu____2778 in
          raise uu____2777
      | FStar_Syntax_Syntax.Tm_uvar uu____2780 ->
          let uu____2789 =
            let uu____2790 =
              let uu____2791 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2791 in
            FStar_Errors.Err uu____2790 in
          raise uu____2789
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2792 =
            let uu____2793 =
              let uu____2794 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2794 in
            FStar_Errors.Err uu____2793 in
          raise uu____2792
      | FStar_Syntax_Syntax.Tm_delayed uu____2795 -> failwith "impossible"
let is_monadic: FStar_Syntax_Syntax.residual_comp option -> Prims.bool =
  fun uu___94_2814  ->
    match uu___94_2814 with
    | None  -> failwith "un-annotated lambda?!"
    | Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___93_2818  ->
                match uu___93_2818 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2819 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2824 =
      let uu____2825 = FStar_Syntax_Subst.compress t in
      uu____2825.FStar_Syntax_Syntax.n in
    match uu____2824 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2845 =
            let uu____2846 = FStar_List.hd args in fst uu____2846 in
          is_C uu____2845 in
        if r
        then
          ((let uu____2858 =
              let uu____2859 =
                FStar_List.for_all
                  (fun uu____2862  ->
                     match uu____2862 with | (h,uu____2866) -> is_C h) args in
              Prims.op_Negation uu____2859 in
            if uu____2858 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2870 =
              let uu____2871 =
                FStar_List.for_all
                  (fun uu____2874  ->
                     match uu____2874 with
                     | (h,uu____2878) ->
                         let uu____2879 = is_C h in
                         Prims.op_Negation uu____2879) args in
              Prims.op_Negation uu____2871 in
            if uu____2870 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2893 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____2893 with
         | M t1 ->
             ((let uu____2896 = is_C t1 in
               if uu____2896 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2900) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2906) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2912,uu____2913) -> is_C t1
    | uu____2942 -> false
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
          let uu____2972 =
            let uu____2973 =
              let uu____2983 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____2984 =
                let uu____2988 =
                  let uu____2991 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____2991) in
                [uu____2988] in
              (uu____2983, uu____2984) in
            FStar_Syntax_Syntax.Tm_app uu____2973 in
          mk1 uu____2972 in
        let uu____2999 =
          let uu____3000 = FStar_Syntax_Syntax.mk_binder p in [uu____3000] in
        FStar_Syntax_Util.abs uu____2999 body
          (Some (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___95_3004  ->
    match uu___95_3004 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3005 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3139 =
          match uu____3139 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3160 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3161 =
                       let uu____3162 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3162 in
                     Prims.op_Negation uu____3161) in
                if uu____3160
                then
                  let uu____3163 =
                    let uu____3164 =
                      let uu____3165 = FStar_Syntax_Print.term_to_string e in
                      let uu____3166 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3167 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3165 uu____3166 uu____3167 in
                    FStar_Errors.Err uu____3164 in
                  raise uu____3163
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3181 = mk_return env t1 s_e in
                     ((M t1), uu____3181, u_e)))
               | (M t1,N t2) ->
                   let uu____3184 =
                     let uu____3185 =
                       let uu____3186 = FStar_Syntax_Print.term_to_string e in
                       let uu____3187 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3188 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3186 uu____3187 uu____3188 in
                     FStar_Errors.Err uu____3185 in
                   raise uu____3184) in
        let ensure_m env1 e2 =
          let strip_m uu___96_3214 =
            match uu___96_3214 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3224 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3235 =
                let uu____3236 =
                  let uu____3239 =
                    let uu____3240 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3240 in
                  (uu____3239, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3236 in
              raise uu____3235
          | M uu____3244 ->
              let uu____3245 = check env1 e2 context_nm in strip_m uu____3245 in
        let uu____3249 =
          let uu____3250 = FStar_Syntax_Subst.compress e in
          uu____3250.FStar_Syntax_Syntax.n in
        match uu____3249 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3256 ->
            let uu____3257 = infer env e in return_if uu____3257
        | FStar_Syntax_Syntax.Tm_name uu____3261 ->
            let uu____3262 = infer env e in return_if uu____3262
        | FStar_Syntax_Syntax.Tm_fvar uu____3266 ->
            let uu____3267 = infer env e in return_if uu____3267
        | FStar_Syntax_Syntax.Tm_abs uu____3271 ->
            let uu____3281 = infer env e in return_if uu____3281
        | FStar_Syntax_Syntax.Tm_constant uu____3285 ->
            let uu____3286 = infer env e in return_if uu____3286
        | FStar_Syntax_Syntax.Tm_app uu____3290 ->
            let uu____3300 = infer env e in return_if uu____3300
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3347) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3353) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3359,uu____3360) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3389 ->
            let uu____3397 =
              let uu____3398 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3398 in
            failwith uu____3397
        | FStar_Syntax_Syntax.Tm_type uu____3402 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3406 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3417 ->
            let uu____3422 =
              let uu____3423 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3423 in
            failwith uu____3422
        | FStar_Syntax_Syntax.Tm_uvar uu____3427 ->
            let uu____3436 =
              let uu____3437 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3437 in
            failwith uu____3436
        | FStar_Syntax_Syntax.Tm_delayed uu____3441 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3459 =
              let uu____3460 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3460 in
            failwith uu____3459
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
      let uu____3482 =
        let uu____3483 = FStar_Syntax_Subst.compress e in
        uu____3483.FStar_Syntax_Syntax.n in
      match uu____3482 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | Some
                { FStar_Syntax_Syntax.residual_effect = uu____3522;
                  FStar_Syntax_Syntax.residual_typ = None ;
                  FStar_Syntax_Syntax.residual_flags = uu____3523;_}
                -> rc_opt1
            | None  -> rc_opt1
            | Some rc ->
                let uu____3528 =
                  let uu___111_3529 = rc in
                  let uu____3530 =
                    let uu____3534 =
                      let uu____3535 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____3535 in
                    Some uu____3534 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___111_3529.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____3530;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___111_3529.FStar_Syntax_Syntax.residual_flags)
                  } in
                Some uu____3528 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___112_3544 = env in
            let uu____3545 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3545;
              subst = (uu___112_3544.subst);
              tc_const = (uu___112_3544.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3554  ->
                 match uu____3554 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_3562 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_3562.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_3562.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3563 =
            FStar_List.fold_left
              (fun uu____3572  ->
                 fun uu____3573  ->
                   match (uu____3572, uu____3573) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3601 = is_C c in
                       if uu____3601
                       then
                         let xw =
                           let uu____3606 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3606 in
                         let x =
                           let uu___114_3608 = bv in
                           let uu____3609 =
                             let uu____3612 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3612 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_3608.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_3608.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3609
                           } in
                         let env3 =
                           let uu___115_3614 = env2 in
                           let uu____3615 =
                             let uu____3617 =
                               let uu____3618 =
                                 let uu____3623 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3623) in
                               FStar_Syntax_Syntax.NT uu____3618 in
                             uu____3617 :: (env2.subst) in
                           {
                             env = (uu___115_3614.env);
                             subst = uu____3615;
                             tc_const = (uu___115_3614.tc_const)
                           } in
                         let uu____3624 =
                           let uu____3626 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3627 =
                             let uu____3629 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3629 :: acc in
                           uu____3626 :: uu____3627 in
                         (env3, uu____3624)
                       else
                         (let x =
                            let uu___116_3633 = bv in
                            let uu____3634 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_3633.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_3633.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3634
                            } in
                          let uu____3637 =
                            let uu____3639 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3639 :: acc in
                          (env2, uu____3637))) (env1, []) binders1 in
          (match uu____3563 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3651 =
                 let check_what =
                   let uu____3663 = is_monadic rc_opt1 in
                   if uu____3663 then check_m else check_n in
                 let uu____3672 = check_what env2 body1 in
                 match uu____3672 with
                 | (t,s_body,u_body) ->
                     let uu____3682 =
                       let uu____3683 =
                         let uu____3684 = is_monadic rc_opt1 in
                         if uu____3684 then M t else N t in
                       comp_of_nm uu____3683 in
                     (uu____3682, s_body, u_body) in
               (match uu____3651 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_rc_opt =
                      match rc_opt1 with
                      | None  -> None
                      | Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | None  ->
                               let rc1 =
                                 let uu____3703 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___97_3705  ->
                                           match uu___97_3705 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____3706 -> false)) in
                                 if uu____3703
                                 then
                                   let uu____3707 =
                                     FStar_List.filter
                                       (fun uu___98_3709  ->
                                          match uu___98_3709 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____3710 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Syntax_Const.effect_Tot_lid None
                                     uu____3707
                                 else rc in
                               Some rc1
                           | Some rt ->
                               let uu____3719 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___99_3721  ->
                                         match uu___99_3721 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____3722 -> false)) in
                               if uu____3719
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___100_3726  ->
                                        match uu___100_3726 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____3727 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____3728 =
                                   let uu____3729 =
                                     let uu____3733 = double_star rt in
                                     Some uu____3733 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Syntax_Const.effect_Tot_lid
                                     uu____3729 flags in
                                 Some uu____3728
                               else
                                 (let uu____3735 =
                                    let uu___117_3736 = rc in
                                    let uu____3737 =
                                      let uu____3741 = star_type' env2 rt in
                                      Some uu____3741 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_3736.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____3737;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_3736.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  Some uu____3735)) in
                    let uu____3742 =
                      let comp1 =
                        let uu____3749 = is_monadic rc_opt1 in
                        let uu____3750 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3749 uu____3750 in
                      let uu____3751 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____3751,
                        (Some (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____3742 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____3784 =
                             let uu____3785 =
                               let uu____3795 =
                                 let uu____3797 =
                                   FStar_Syntax_Subst.closing_subst
                                     s_binders1 in
                                 subst_rc_opt uu____3797 s_rc_opt in
                               (s_binders1, s_body1, uu____3795) in
                             FStar_Syntax_Syntax.Tm_abs uu____3785 in
                           mk1 uu____3784 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____3805 =
                             let uu____3806 =
                               let uu____3816 =
                                 let uu____3818 =
                                   FStar_Syntax_Subst.closing_subst
                                     u_binders2 in
                                 subst_rc_opt uu____3818 u_rc_opt in
                               (u_binders2, u_body2, uu____3816) in
                             FStar_Syntax_Syntax.Tm_abs uu____3806 in
                           mk1 uu____3805 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.ty = uu____3826;
                FStar_Syntax_Syntax.p = uu____3827;_};
            FStar_Syntax_Syntax.fv_delta = uu____3828;
            FStar_Syntax_Syntax.fv_qual = uu____3829;_}
          ->
          let uu____3835 =
            let uu____3838 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____3838 in
          (match uu____3835 with
           | (uu____3854,t) ->
               let uu____3856 = let uu____3857 = normalize1 t in N uu____3857 in
               (uu____3856, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3874 = check_n env head1 in
          (match uu____3874 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3888 =
                   let uu____3889 = FStar_Syntax_Subst.compress t in
                   uu____3889.FStar_Syntax_Syntax.n in
                 match uu____3888 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3892 -> true
                 | uu____3900 -> false in
               let rec flatten1 t =
                 let uu____3912 =
                   let uu____3913 = FStar_Syntax_Subst.compress t in
                   uu____3913.FStar_Syntax_Syntax.n in
                 match uu____3912 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____3925);
                                FStar_Syntax_Syntax.tk = uu____3926;
                                FStar_Syntax_Syntax.pos = uu____3927;
                                FStar_Syntax_Syntax.vars = uu____3928;_})
                     when is_arrow t1 ->
                     let uu____3945 = flatten1 t1 in
                     (match uu____3945 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3997,uu____3998)
                     -> flatten1 e1
                 | uu____4027 ->
                     let uu____4028 =
                       let uu____4029 =
                         let uu____4030 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4030 in
                       FStar_Errors.Err uu____4029 in
                     raise uu____4028 in
               let uu____4038 = flatten1 t_head in
               (match uu____4038 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4090 =
                          let uu____4091 =
                            let uu____4092 = FStar_Util.string_of_int n1 in
                            let uu____4099 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4110 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4092 uu____4099 uu____4110 in
                          FStar_Errors.Err uu____4091 in
                        raise uu____4090)
                     else ();
                     (let uu____4118 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4118 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4145 args1 =
                            match uu____4145 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4188 =
                                       let uu____4189 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4189.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4188
                                 | (binders3,[]) ->
                                     let uu____4208 =
                                       let uu____4209 =
                                         let uu____4212 =
                                           let uu____4213 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4213 in
                                         FStar_Syntax_Subst.compress
                                           uu____4212 in
                                       uu____4209.FStar_Syntax_Syntax.n in
                                     (match uu____4208 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4229 =
                                            let uu____4230 =
                                              let uu____4231 =
                                                let uu____4239 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4239) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4231 in
                                            mk1 uu____4230 in
                                          N uu____4229
                                      | uu____4243 -> failwith "wat?")
                                 | ([],uu____4244::uu____4245) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4270)::binders3,(arg,uu____4273)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4307 = FStar_List.splitAt n' binders1 in
                          (match uu____4307 with
                           | (binders2,uu____4326) ->
                               let uu____4339 =
                                 let uu____4349 =
                                   FStar_List.map2
                                     (fun uu____4369  ->
                                        fun uu____4370  ->
                                          match (uu____4369, uu____4370) with
                                          | ((bv,uu____4387),(arg,q)) ->
                                              let uu____4394 =
                                                let uu____4395 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4395.FStar_Syntax_Syntax.n in
                                              (match uu____4394 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4405 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4418 ->
                                                   let uu____4419 =
                                                     check_n env arg in
                                                   (match uu____4419 with
                                                    | (uu____4430,s_arg,u_arg)
                                                        ->
                                                        let uu____4433 =
                                                          let uu____4437 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4437
                                                          then
                                                            let uu____4441 =
                                                              let uu____4444
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4444, q) in
                                                            [uu____4441;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4433))))
                                     binders2 args in
                                 FStar_List.split uu____4349 in
                               (match uu____4339 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4491 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4497 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4491, uu____4497)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4546) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4552) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4558,uu____4559) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4589 = let uu____4590 = env.tc_const c in N uu____4590 in
          (uu____4589, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4591 ->
          let uu____4599 =
            let uu____4600 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4600 in
          failwith uu____4599
      | FStar_Syntax_Syntax.Tm_type uu____4604 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4608 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4619 ->
          let uu____4624 =
            let uu____4625 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4625 in
          failwith uu____4624
      | FStar_Syntax_Syntax.Tm_uvar uu____4629 ->
          let uu____4638 =
            let uu____4639 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4639 in
          failwith uu____4638
      | FStar_Syntax_Syntax.Tm_delayed uu____4643 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4661 =
            let uu____4662 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4662 in
          failwith uu____4661
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
          let uu____4700 = check_n env e0 in
          match uu____4700 with
          | (uu____4707,s_e0,u_e0) ->
              let uu____4710 =
                let uu____4728 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4761 = FStar_Syntax_Subst.open_branch b in
                       match uu____4761 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___118_4793 = env in
                             let uu____4794 =
                               let uu____4795 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4795 in
                             {
                               env = uu____4794;
                               subst = (uu___118_4793.subst);
                               tc_const = (uu___118_4793.tc_const)
                             } in
                           let uu____4797 = f env1 body in
                           (match uu____4797 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4846 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4728 in
              (match uu____4710 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____4911 = FStar_List.hd nms in
                     match uu____4911 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___101_4915  ->
                          match uu___101_4915 with
                          | M uu____4916 -> true
                          | uu____4917 -> false) nms in
                   let uu____4918 =
                     let uu____4941 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____4993  ->
                              match uu____4993 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5116 =
                                         check env original_body (M t2) in
                                       (match uu____5116 with
                                        | (uu____5139,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5168,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____4941 in
                   (match uu____4918 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5287  ->
                                 match uu____5287 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5328 =
                                         let uu____5329 =
                                           let uu____5339 =
                                             let uu____5343 =
                                               let uu____5346 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5347 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5346, uu____5347) in
                                             [uu____5343] in
                                           (s_body, uu____5339) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5329 in
                                       mk1 uu____5328 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5369 =
                              let uu____5370 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5370] in
                            let uu____5371 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____5369 uu____5371
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____5376 =
                              let uu____5380 =
                                let uu____5381 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5381 in
                              [uu____5380] in
                            let uu____5382 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5376 uu____5382 in
                          let uu____5385 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5415 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5385, uu____5415)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5429 =
                             let uu____5432 =
                               let uu____5433 =
                                 let uu____5451 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5451,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5433 in
                             mk1 uu____5432 in
                           let uu____5478 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5429, uu____5478))))
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
              let uu____5521 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5521] in
            let uu____5522 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5522 with
            | (x_binders1,e21) ->
                let uu____5530 = infer env e1 in
                (match uu____5530 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5541 = is_C t1 in
                       if uu____5541
                       then
                         let uu___119_5542 = binding in
                         let uu____5543 =
                           let uu____5546 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5546 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_5542.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_5542.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5543;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_5542.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_5542.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_5549 = env in
                       let uu____5550 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_5551 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_5551.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_5551.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5550;
                         subst = (uu___120_5549.subst);
                         tc_const = (uu___120_5549.tc_const)
                       } in
                     let uu____5552 = proceed env1 e21 in
                     (match uu____5552 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_5563 = binding in
                            let uu____5564 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_5563.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_5563.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5564;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_5563.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_5563.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5567 =
                            let uu____5570 =
                              let uu____5571 =
                                let uu____5579 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_5584 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_5584.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_5584.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_5584.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_5584.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5579) in
                              FStar_Syntax_Syntax.Tm_let uu____5571 in
                            mk1 uu____5570 in
                          let uu____5585 =
                            let uu____5588 =
                              let uu____5589 =
                                let uu____5597 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_5602 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_5602.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_5602.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_5602.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_5602.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5597) in
                              FStar_Syntax_Syntax.Tm_let uu____5589 in
                            mk1 uu____5588 in
                          (nm_rec, uu____5567, uu____5585))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_5611 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_5611.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_5611.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_5611.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_5613 = env in
                       let uu____5614 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_5615 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_5615.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_5615.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5614;
                         subst = (uu___126_5613.subst);
                         tc_const = (uu___126_5613.tc_const)
                       } in
                     let uu____5616 = ensure_m env1 e21 in
                     (match uu____5616 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____5633 =
                              let uu____5634 =
                                let uu____5644 =
                                  let uu____5648 =
                                    let uu____5651 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5652 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5651, uu____5652) in
                                  [uu____5648] in
                                (s_e2, uu____5644) in
                              FStar_Syntax_Syntax.Tm_app uu____5634 in
                            mk1 uu____5633 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____5664 =
                              let uu____5665 =
                                let uu____5675 =
                                  let uu____5679 =
                                    let uu____5682 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5682) in
                                  [uu____5679] in
                                (s_e1, uu____5675) in
                              FStar_Syntax_Syntax.Tm_app uu____5665 in
                            mk1 uu____5664 in
                          let uu____5690 =
                            let uu____5691 =
                              let uu____5692 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5692] in
                            FStar_Syntax_Util.abs uu____5691 body
                              (Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____5693 =
                            let uu____5696 =
                              let uu____5697 =
                                let uu____5705 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_5710 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_5710.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_5710.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_5710.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_5710.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5705) in
                              FStar_Syntax_Syntax.Tm_let uu____5697 in
                            mk1 uu____5696 in
                          ((M t2), uu____5690, uu____5693)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5719 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____5719 in
      let uu____5724 = check env e mn in
      match uu____5724 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5734 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5747 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____5747 in
      let uu____5752 = check env e mn in
      match uu____5752 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5762 -> failwith "[check_m]: impossible"
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
        (let uu____5784 =
           let uu____5785 = is_C c in Prims.op_Negation uu____5785 in
         if uu____5784 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____5797 =
           let uu____5798 = FStar_Syntax_Subst.compress c in
           uu____5798.FStar_Syntax_Syntax.n in
         match uu____5797 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5817 = FStar_Syntax_Util.head_and_args wp in
             (match uu____5817 with
              | (wp_head,wp_args) ->
                  ((let uu____5844 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5861 =
                           let uu____5862 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5862 in
                         Prims.op_Negation uu____5861) in
                    if uu____5844 then failwith "mismatch" else ());
                   (let uu____5874 =
                      let uu____5875 =
                        let uu____5885 =
                          FStar_List.map2
                            (fun uu____5895  ->
                               fun uu____5896  ->
                                 match (uu____5895, uu____5896) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____5919 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____5919
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____5922 = print_implicit q in
                                         let uu____5923 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____5922 uu____5923)
                                      else ();
                                      (let uu____5925 =
                                         trans_F_ env arg wp_arg in
                                       (uu____5925, q)))) args wp_args in
                        (head1, uu____5885) in
                      FStar_Syntax_Syntax.Tm_app uu____5875 in
                    mk1 uu____5874)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____5947 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____5947 with
              | (binders_orig,comp1) ->
                  let uu____5952 =
                    let uu____5960 =
                      FStar_List.map
                        (fun uu____5974  ->
                           match uu____5974 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____5987 = is_C h in
                               if uu____5987
                               then
                                 let w' =
                                   let uu____5994 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____5994 in
                                 let uu____5995 =
                                   let uu____5999 =
                                     let uu____6003 =
                                       let uu____6006 =
                                         let uu____6007 =
                                           let uu____6008 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6008 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6007 in
                                       (uu____6006, q) in
                                     [uu____6003] in
                                   (w', q) :: uu____5999 in
                                 (w', uu____5995)
                               else
                                 (let x =
                                    let uu____6020 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6020 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____5960 in
                  (match uu____5952 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6050 =
                           let uu____6052 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6052 in
                         FStar_Syntax_Subst.subst_comp uu____6050 comp1 in
                       let app =
                         let uu____6056 =
                           let uu____6057 =
                             let uu____6067 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6074 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6075 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6074, uu____6075)) bvs in
                             (wp, uu____6067) in
                           FStar_Syntax_Syntax.Tm_app uu____6057 in
                         mk1 uu____6056 in
                       let comp3 =
                         let uu____6080 = type_of_comp comp2 in
                         let uu____6081 = is_monadic_comp comp2 in
                         trans_G env uu____6080 uu____6081 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6083,uu____6084) ->
             trans_F_ env e wp
         | uu____6113 -> failwith "impossible trans_F_")
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
            let uu____6118 =
              let uu____6119 = star_type' env h in
              let uu____6122 =
                let uu____6128 =
                  let uu____6131 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6131) in
                [uu____6128] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6119;
                FStar_Syntax_Syntax.effect_args = uu____6122;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6118
          else
            (let uu____6137 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6137)
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
    fun t  -> let uu____6152 = n env.env t in star_type' env uu____6152
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6166 = n env.env t in check_n env uu____6166
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6179 = n env.env c in
        let uu____6180 = n env.env wp in trans_F_ env uu____6179 uu____6180