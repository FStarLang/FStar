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
              let uu___101_94 = a in
              let uu____95 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___101_94.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___101_94.FStar_Syntax_Syntax.index);
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
                  let uu____334 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____335 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____334, uu____335) in
                match uu____295 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____366 =
                        let uu____367 =
                          let uu____377 =
                            let uu____381 =
                              FStar_List.map
                                (fun uu____389  ->
                                   match uu____389 with
                                   | (bv,uu____395) ->
                                       let uu____396 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____397 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____396, uu____397)) binders in
                            let uu____398 =
                              let uu____402 =
                                let uu____405 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____406 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____405, uu____406) in
                              let uu____407 =
                                let uu____411 =
                                  let uu____414 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____414) in
                                [uu____411] in
                              uu____402 :: uu____407 in
                            FStar_List.append uu____381 uu____398 in
                          (fv, uu____377) in
                        FStar_Syntax_Syntax.Tm_app uu____367 in
                      mk1 uu____366 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____283 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____460 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____460 in
                    let ret1 =
                      let uu____468 =
                        let uu____474 =
                          let uu____475 =
                            let uu____478 =
                              let uu____479 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____479 in
                            FStar_Syntax_Syntax.mk_Total uu____478 in
                          FStar_Syntax_Util.lcomp_of_comp uu____475 in
                        FStar_Util.Inl uu____474 in
                      Some uu____468 in
                    let body =
                      let uu____489 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____489 ret1 in
                    let uu____490 =
                      let uu____491 = mk_all_implicit binders in
                      let uu____495 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____491 uu____495 in
                    FStar_Syntax_Util.abs uu____490 body ret1 in
                  let c_pure1 =
                    let uu____510 = mk_lid "pure" in
                    register env1 uu____510 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____515 =
                        let uu____516 =
                          let uu____517 =
                            let uu____521 =
                              let uu____522 =
                                let uu____523 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____523 in
                              FStar_Syntax_Syntax.mk_binder uu____522 in
                            [uu____521] in
                          let uu____524 =
                            let uu____527 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____527 in
                          FStar_Syntax_Util.arrow uu____517 uu____524 in
                        mk_gctx uu____516 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____515 in
                    let r =
                      let uu____529 =
                        let uu____530 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____530 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____529 in
                    let ret1 =
                      let uu____538 =
                        let uu____544 =
                          let uu____545 =
                            let uu____548 =
                              let uu____549 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____549 in
                            FStar_Syntax_Syntax.mk_Total uu____548 in
                          FStar_Syntax_Util.lcomp_of_comp uu____545 in
                        FStar_Util.Inl uu____544 in
                      Some uu____538 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____564 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____567 =
                          let uu____573 =
                            let uu____575 =
                              let uu____576 =
                                let uu____577 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____577
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____576 in
                            [uu____575] in
                          FStar_List.append gamma_as_args uu____573 in
                        FStar_Syntax_Util.mk_app uu____564 uu____567 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____580 =
                      let uu____581 = mk_all_implicit binders in
                      let uu____585 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____581 uu____585 in
                    FStar_Syntax_Util.abs uu____580 outer_body ret1 in
                  let c_app1 =
                    let uu____604 = mk_lid "app" in
                    register env1 uu____604 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____611 =
                        let uu____615 =
                          let uu____616 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____616 in
                        [uu____615] in
                      let uu____617 =
                        let uu____620 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____620 in
                      FStar_Syntax_Util.arrow uu____611 uu____617 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____623 =
                        let uu____624 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____624 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____623 in
                    let ret1 =
                      let uu____632 =
                        let uu____638 =
                          let uu____639 =
                            let uu____642 =
                              let uu____643 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____643 in
                            FStar_Syntax_Syntax.mk_Total uu____642 in
                          FStar_Syntax_Util.lcomp_of_comp uu____639 in
                        FStar_Util.Inl uu____638 in
                      Some uu____632 in
                    let uu____652 =
                      let uu____653 = mk_all_implicit binders in
                      let uu____657 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____653 uu____657 in
                    let uu____675 =
                      let uu____676 =
                        let uu____682 =
                          let uu____684 =
                            let uu____687 =
                              let uu____693 =
                                let uu____695 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____695] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____693 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____687 in
                          let uu____696 =
                            let uu____700 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____700] in
                          uu____684 :: uu____696 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____682 in
                      FStar_Syntax_Util.mk_app c_app1 uu____676 in
                    FStar_Syntax_Util.abs uu____652 uu____675 ret1 in
                  let c_lift11 =
                    let uu____704 = mk_lid "lift1" in
                    register env1 uu____704 c_lift1 in
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
                      let uu____712 =
                        let uu____716 =
                          let uu____717 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____717 in
                        let uu____718 =
                          let uu____720 =
                            let uu____721 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____721 in
                          [uu____720] in
                        uu____716 :: uu____718 in
                      let uu____722 =
                        let uu____725 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____725 in
                      FStar_Syntax_Util.arrow uu____712 uu____722 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____728 =
                        let uu____729 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____729 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____728 in
                    let a2 =
                      let uu____731 =
                        let uu____732 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____732 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____731 in
                    let ret1 =
                      let uu____740 =
                        let uu____746 =
                          let uu____747 =
                            let uu____750 =
                              let uu____751 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____751 in
                            FStar_Syntax_Syntax.mk_Total uu____750 in
                          FStar_Syntax_Util.lcomp_of_comp uu____747 in
                        FStar_Util.Inl uu____746 in
                      Some uu____740 in
                    let uu____760 =
                      let uu____761 = mk_all_implicit binders in
                      let uu____765 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____761 uu____765 in
                    let uu____787 =
                      let uu____788 =
                        let uu____794 =
                          let uu____796 =
                            let uu____799 =
                              let uu____805 =
                                let uu____807 =
                                  let uu____810 =
                                    let uu____816 =
                                      let uu____818 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____818] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____816 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____810 in
                                let uu____819 =
                                  let uu____823 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____823] in
                                uu____807 :: uu____819 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____805 in
                            FStar_Syntax_Util.mk_app c_app1 uu____799 in
                          let uu____826 =
                            let uu____830 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____830] in
                          uu____796 :: uu____826 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____794 in
                      FStar_Syntax_Util.mk_app c_app1 uu____788 in
                    FStar_Syntax_Util.abs uu____760 uu____787 ret1 in
                  let c_lift21 =
                    let uu____834 = mk_lid "lift2" in
                    register env1 uu____834 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____841 =
                        let uu____845 =
                          let uu____846 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____846 in
                        [uu____845] in
                      let uu____847 =
                        let uu____850 =
                          let uu____851 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____851 in
                        FStar_Syntax_Syntax.mk_Total uu____850 in
                      FStar_Syntax_Util.arrow uu____841 uu____847 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let ret1 =
                      let uu____860 =
                        let uu____866 =
                          let uu____867 =
                            let uu____870 =
                              let uu____871 =
                                let uu____872 =
                                  let uu____876 =
                                    let uu____877 =
                                      FStar_Syntax_Syntax.bv_to_name t1 in
                                    FStar_Syntax_Syntax.null_binder uu____877 in
                                  [uu____876] in
                                let uu____878 =
                                  let uu____881 =
                                    FStar_Syntax_Syntax.bv_to_name t2 in
                                  FStar_Syntax_Syntax.mk_GTotal uu____881 in
                                FStar_Syntax_Util.arrow uu____872 uu____878 in
                              mk_ctx uu____871 in
                            FStar_Syntax_Syntax.mk_Total uu____870 in
                          FStar_Syntax_Util.lcomp_of_comp uu____867 in
                        FStar_Util.Inl uu____866 in
                      Some uu____860 in
                    let e1 =
                      let uu____891 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____891 in
                    let body =
                      let uu____893 =
                        let uu____894 =
                          let uu____898 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____898] in
                        FStar_List.append gamma uu____894 in
                      let uu____901 =
                        let uu____902 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____905 =
                          let uu____911 =
                            let uu____912 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____912 in
                          let uu____913 = args_of_binders1 gamma in uu____911
                            :: uu____913 in
                        FStar_Syntax_Util.mk_app uu____902 uu____905 in
                      FStar_Syntax_Util.abs uu____893 uu____901 ret1 in
                    let uu____915 =
                      let uu____916 = mk_all_implicit binders in
                      let uu____920 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____916 uu____920 in
                    FStar_Syntax_Util.abs uu____915 body ret1 in
                  let c_push1 =
                    let uu____937 = mk_lid "push" in
                    register env1 uu____937 c_push in
                  let ret_tot_wp_a =
                    let uu____945 =
                      let uu____951 =
                        let uu____952 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____952 in
                      FStar_Util.Inl uu____951 in
                    Some uu____945 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____983 =
                        let uu____984 =
                          let uu____994 = args_of_binders1 binders in
                          (c, uu____994) in
                        FStar_Syntax_Syntax.Tm_app uu____984 in
                      mk1 uu____983
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1002 =
                        let uu____1003 =
                          let uu____1007 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____1008 =
                            let uu____1010 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____1010] in
                          uu____1007 :: uu____1008 in
                        let uu____1011 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____1003 uu____1011 in
                      FStar_Syntax_Syntax.mk_Total uu____1002 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____1015 =
                      let uu____1016 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1016 in
                    let uu____1022 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____1024 =
                        let uu____1027 =
                          let uu____1033 =
                            let uu____1035 =
                              let uu____1038 =
                                let uu____1044 =
                                  let uu____1045 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1045 in
                                [uu____1044] in
                              FStar_Syntax_Util.mk_app l_ite uu____1038 in
                            [uu____1035] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1033 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1027 in
                      FStar_Syntax_Util.ascribe uu____1024
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____1015 uu____1022
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1070 = mk_lid "wp_if_then_else" in
                    register env1 uu____1070 wp_if_then_else in
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
                      let uu____1081 =
                        let uu____1087 =
                          let uu____1089 =
                            let uu____1092 =
                              let uu____1098 =
                                let uu____1100 =
                                  let uu____1103 =
                                    let uu____1109 =
                                      let uu____1110 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1110 in
                                    [uu____1109] in
                                  FStar_Syntax_Util.mk_app l_and uu____1103 in
                                [uu____1100] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1098 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1092 in
                          let uu____1115 =
                            let uu____1119 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1119] in
                          uu____1089 :: uu____1115 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1087 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1081 in
                    let uu____1122 =
                      let uu____1123 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1123 in
                    FStar_Syntax_Util.abs uu____1122 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____1130 = mk_lid "wp_assert" in
                    register env1 uu____1130 wp_assert in
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
                      let uu____1141 =
                        let uu____1147 =
                          let uu____1149 =
                            let uu____1152 =
                              let uu____1158 =
                                let uu____1160 =
                                  let uu____1163 =
                                    let uu____1169 =
                                      let uu____1170 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1170 in
                                    [uu____1169] in
                                  FStar_Syntax_Util.mk_app l_imp uu____1163 in
                                [uu____1160] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1158 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1152 in
                          let uu____1175 =
                            let uu____1179 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1179] in
                          uu____1149 :: uu____1175 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1147 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1141 in
                    let uu____1182 =
                      let uu____1183 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1183 in
                    FStar_Syntax_Util.abs uu____1182 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1190 = mk_lid "wp_assume" in
                    register env1 uu____1190 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1199 =
                        let uu____1203 =
                          let uu____1204 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1204 in
                        [uu____1203] in
                      let uu____1205 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1199 uu____1205 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1212 =
                        let uu____1218 =
                          let uu____1220 =
                            let uu____1223 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1223 in
                          let uu____1229 =
                            let uu____1233 =
                              let uu____1236 =
                                let uu____1242 =
                                  let uu____1244 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1244] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1242 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1236 in
                            [uu____1233] in
                          uu____1220 :: uu____1229 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1218 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1212 in
                    let uu____1251 =
                      let uu____1252 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1252 in
                    FStar_Syntax_Util.abs uu____1251 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1259 = mk_lid "wp_close" in
                    register env1 uu____1259 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1270 =
                      let uu____1276 =
                        let uu____1277 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1277 in
                      FStar_Util.Inl uu____1276 in
                    Some uu____1270 in
                  let ret_gtot_type =
                    let uu____1297 =
                      let uu____1303 =
                        let uu____1304 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1304 in
                      FStar_Util.Inl uu____1303 in
                    Some uu____1297 in
                  let mk_forall1 x body =
                    let uu____1324 =
                      let uu____1327 =
                        let uu____1328 =
                          let uu____1338 =
                            let uu____1340 =
                              let uu____1341 =
                                let uu____1342 =
                                  let uu____1343 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1343] in
                                FStar_Syntax_Util.abs uu____1342 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1341 in
                            [uu____1340] in
                          (FStar_Syntax_Util.tforall, uu____1338) in
                        FStar_Syntax_Syntax.Tm_app uu____1328 in
                      FStar_Syntax_Syntax.mk uu____1327 in
                    uu____1324 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1357 =
                      let uu____1358 = FStar_Syntax_Subst.compress t in
                      uu____1358.FStar_Syntax_Syntax.n in
                    match uu____1357 with
                    | FStar_Syntax_Syntax.Tm_type uu____1361 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1376  ->
                              match uu____1376 with
                              | (b,uu____1380) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1381 -> true in
                  let rec is_monotonic t =
                    let uu____1386 =
                      let uu____1387 = FStar_Syntax_Subst.compress t in
                      uu____1387.FStar_Syntax_Syntax.n in
                    match uu____1386 with
                    | FStar_Syntax_Syntax.Tm_type uu____1390 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1405  ->
                              match uu____1405 with
                              | (b,uu____1409) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1410 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1462 =
                      let uu____1463 = FStar_Syntax_Subst.compress t1 in
                      uu____1463.FStar_Syntax_Syntax.n in
                    match uu____1462 with
                    | FStar_Syntax_Syntax.Tm_type uu____1466 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1469);
                                      FStar_Syntax_Syntax.tk = uu____1470;
                                      FStar_Syntax_Syntax.pos = uu____1471;
                                      FStar_Syntax_Syntax.vars = uu____1472;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1495 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1495
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1498 =
                              let uu____1501 =
                                let uu____1507 =
                                  let uu____1508 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1508 in
                                [uu____1507] in
                              FStar_Syntax_Util.mk_app x uu____1501 in
                            let uu____1509 =
                              let uu____1512 =
                                let uu____1518 =
                                  let uu____1519 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1519 in
                                [uu____1518] in
                              FStar_Syntax_Util.mk_app y uu____1512 in
                            mk_rel1 b uu____1498 uu____1509 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1524 =
                               let uu____1525 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1528 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1525 uu____1528 in
                             let uu____1531 =
                               let uu____1532 =
                                 let uu____1535 =
                                   let uu____1541 =
                                     let uu____1542 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1542 in
                                   [uu____1541] in
                                 FStar_Syntax_Util.mk_app x uu____1535 in
                               let uu____1543 =
                                 let uu____1546 =
                                   let uu____1552 =
                                     let uu____1553 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1553 in
                                   [uu____1552] in
                                 FStar_Syntax_Util.mk_app y uu____1546 in
                               mk_rel1 b uu____1532 uu____1543 in
                             FStar_Syntax_Util.mk_imp uu____1524 uu____1531 in
                           let uu____1554 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1554)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1557);
                                      FStar_Syntax_Syntax.tk = uu____1558;
                                      FStar_Syntax_Syntax.pos = uu____1559;
                                      FStar_Syntax_Syntax.vars = uu____1560;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1583 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1583
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1586 =
                              let uu____1589 =
                                let uu____1595 =
                                  let uu____1596 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1596 in
                                [uu____1595] in
                              FStar_Syntax_Util.mk_app x uu____1589 in
                            let uu____1597 =
                              let uu____1600 =
                                let uu____1606 =
                                  let uu____1607 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1607 in
                                [uu____1606] in
                              FStar_Syntax_Util.mk_app y uu____1600 in
                            mk_rel1 b uu____1586 uu____1597 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1612 =
                               let uu____1613 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1616 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1613 uu____1616 in
                             let uu____1619 =
                               let uu____1620 =
                                 let uu____1623 =
                                   let uu____1629 =
                                     let uu____1630 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1630 in
                                   [uu____1629] in
                                 FStar_Syntax_Util.mk_app x uu____1623 in
                               let uu____1631 =
                                 let uu____1634 =
                                   let uu____1640 =
                                     let uu____1641 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1641 in
                                   [uu____1640] in
                                 FStar_Syntax_Util.mk_app y uu____1634 in
                               mk_rel1 b uu____1620 uu____1631 in
                             FStar_Syntax_Util.mk_imp uu____1612 uu____1619 in
                           let uu____1642 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1642)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___102_1663 = t1 in
                          let uu____1664 =
                            let uu____1665 =
                              let uu____1673 =
                                let uu____1674 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1674 in
                              ([binder], uu____1673) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1665 in
                          {
                            FStar_Syntax_Syntax.n = uu____1664;
                            FStar_Syntax_Syntax.tk =
                              (uu___102_1663.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___102_1663.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___102_1663.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1686 ->
                        failwith "unhandled arrow"
                    | uu____1694 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1709 =
                        let uu____1710 = FStar_Syntax_Subst.compress t1 in
                        uu____1710.FStar_Syntax_Syntax.n in
                      match uu____1709 with
                      | FStar_Syntax_Syntax.Tm_type uu____1713 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1730 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1730
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1745 =
                                let uu____1746 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1746 i in
                              FStar_Syntax_Syntax.fvar uu____1745
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1770 =
                            let uu____1774 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1779  ->
                                     match uu____1779 with
                                     | (t2,q) ->
                                         let uu____1784 = project i x in
                                         let uu____1785 = project i y in
                                         mk_stronger t2 uu____1784 uu____1785)
                                args in
                            match uu____1774 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1770 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1802);
                                      FStar_Syntax_Syntax.tk = uu____1803;
                                      FStar_Syntax_Syntax.pos = uu____1804;
                                      FStar_Syntax_Syntax.vars = uu____1805;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1827  ->
                                   match uu____1827 with
                                   | (bv,q) ->
                                       let uu____1832 =
                                         let uu____1833 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1833 in
                                       FStar_Syntax_Syntax.gen_bv uu____1832
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1837 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1837) bvs in
                          let body =
                            let uu____1839 = FStar_Syntax_Util.mk_app x args in
                            let uu____1840 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1839 uu____1840 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1845);
                                      FStar_Syntax_Syntax.tk = uu____1846;
                                      FStar_Syntax_Syntax.pos = uu____1847;
                                      FStar_Syntax_Syntax.vars = uu____1848;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1870  ->
                                   match uu____1870 with
                                   | (bv,q) ->
                                       let uu____1875 =
                                         let uu____1876 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1876 in
                                       FStar_Syntax_Syntax.gen_bv uu____1875
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1880 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1880) bvs in
                          let body =
                            let uu____1882 = FStar_Syntax_Util.mk_app x args in
                            let uu____1883 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1882 uu____1883 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1886 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1888 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1889 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1890 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1888 uu____1889 uu____1890 in
                    let uu____1891 =
                      let uu____1892 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1892 in
                    FStar_Syntax_Util.abs uu____1891 body ret_tot_type in
                  let stronger1 =
                    let uu____1907 = mk_lid "stronger" in
                    register env1 uu____1907 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1913 = FStar_Util.prefix gamma in
                    match uu____1913 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1939 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1939 in
                          let uu____1942 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1942 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1950 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1950 in
                              let guard_free1 =
                                let uu____1957 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1957 in
                              let pat =
                                let uu____1961 =
                                  let uu____1967 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1967] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1961 in
                              let pattern_guarded_body =
                                let uu____1971 =
                                  let uu____1972 =
                                    let uu____1977 =
                                      let uu____1978 =
                                        let uu____1985 =
                                          let uu____1987 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1987] in
                                        [uu____1985] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1978 in
                                    (body, uu____1977) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1972 in
                                mk1 uu____1971 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1990 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1993 =
                            let uu____1994 =
                              let uu____1995 =
                                let uu____1996 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1999 =
                                  let uu____2005 = args_of_binders1 wp_args in
                                  let uu____2007 =
                                    let uu____2009 =
                                      let uu____2010 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____2010 in
                                    [uu____2009] in
                                  FStar_List.append uu____2005 uu____2007 in
                                FStar_Syntax_Util.mk_app uu____1996
                                  uu____1999 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1995 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1994 in
                          FStar_Syntax_Util.abs gamma uu____1993
                            ret_gtot_type in
                        let uu____2011 =
                          let uu____2012 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____2012 in
                        FStar_Syntax_Util.abs uu____2011 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2019 = mk_lid "wp_ite" in
                    register env1 uu____2019 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2025 = FStar_Util.prefix gamma in
                    match uu____2025 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2049 =
                            let uu____2050 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2053 =
                              let uu____2059 =
                                let uu____2060 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2060 in
                              [uu____2059] in
                            FStar_Syntax_Util.mk_app uu____2050 uu____2053 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2049 in
                        let uu____2061 =
                          let uu____2062 =
                            let uu____2066 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2066 gamma in
                          FStar_List.append binders uu____2062 in
                        FStar_Syntax_Util.abs uu____2061 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2075 = mk_lid "null_wp" in
                    register env1 uu____2075 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2084 =
                        let uu____2090 =
                          let uu____2092 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2093 =
                            let uu____2095 =
                              let uu____2098 =
                                let uu____2104 =
                                  let uu____2105 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2105 in
                                [uu____2104] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2098 in
                            let uu____2106 =
                              let uu____2110 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2110] in
                            uu____2095 :: uu____2106 in
                          uu____2092 :: uu____2093 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2090 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2084 in
                    let uu____2113 =
                      let uu____2114 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2114 in
                    FStar_Syntax_Util.abs uu____2113 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2121 = mk_lid "wp_trivial" in
                    register env1 uu____2121 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2126 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2126
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2131 =
                      let uu____2133 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2133 in
                    let uu____2138 =
                      let uu___103_2139 = ed in
                      let uu____2140 =
                        let uu____2141 = c wp_if_then_else2 in
                        ([], uu____2141) in
                      let uu____2143 =
                        let uu____2144 = c wp_ite2 in ([], uu____2144) in
                      let uu____2146 =
                        let uu____2147 = c stronger2 in ([], uu____2147) in
                      let uu____2149 =
                        let uu____2150 = c wp_close2 in ([], uu____2150) in
                      let uu____2152 =
                        let uu____2153 = c wp_assert2 in ([], uu____2153) in
                      let uu____2155 =
                        let uu____2156 = c wp_assume2 in ([], uu____2156) in
                      let uu____2158 =
                        let uu____2159 = c null_wp2 in ([], uu____2159) in
                      let uu____2161 =
                        let uu____2162 = c wp_trivial2 in ([], uu____2162) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_2139.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_2139.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_2139.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_2139.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_2139.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_2139.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_2139.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2140;
                        FStar_Syntax_Syntax.ite_wp = uu____2143;
                        FStar_Syntax_Syntax.stronger = uu____2146;
                        FStar_Syntax_Syntax.close_wp = uu____2149;
                        FStar_Syntax_Syntax.assert_p = uu____2152;
                        FStar_Syntax_Syntax.assume_p = uu____2155;
                        FStar_Syntax_Syntax.null_wp = uu____2158;
                        FStar_Syntax_Syntax.trivial = uu____2161;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_2139.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_2139.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_2139.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_2139.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2131, uu____2138)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_2177 = dmff_env in
      {
        env = env';
        subst = (uu___104_2177.subst);
        tc_const = (uu___104_2177.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2191 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2205 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___90_2217  ->
    match uu___90_2217 with
    | FStar_Syntax_Syntax.Total (t,uu____2219) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___89_2228  ->
                match uu___89_2228 with
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
  fun uu___91_2243  ->
    match uu___91_2243 with
    | N t ->
        let uu____2245 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2245
    | M t ->
        let uu____2247 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2247
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2252,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2254;
                      FStar_Syntax_Syntax.pos = uu____2255;
                      FStar_Syntax_Syntax.vars = uu____2256;_})
        -> nm_of_comp n2
    | uu____2267 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2281 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2281 with | M uu____2282 -> true | N uu____2283 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2288 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2299 =
        let uu____2303 =
          let uu____2304 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2304 in
        [uu____2303] in
      let uu____2305 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2299 uu____2305 in
    let uu____2308 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2308
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
          (let uu____2343 =
             let uu____2351 =
               let uu____2355 =
                 let uu____2358 =
                   let uu____2359 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2359 in
                 let uu____2360 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2358, uu____2360) in
               [uu____2355] in
             let uu____2365 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2351, uu____2365) in
           FStar_Syntax_Syntax.Tm_arrow uu____2343)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2394) ->
          let binders1 =
            FStar_List.map
              (fun uu____2413  ->
                 match uu____2413 with
                 | (bv,aqual) ->
                     let uu____2420 =
                       let uu___105_2421 = bv in
                       let uu____2422 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_2421.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_2421.FStar_Syntax_Syntax.index);
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
                        (let uu____2563 = f x1 in
                         FStar_Util.string_builder_append strb uu____2563))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2565 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2566 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2565 uu____2566 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2574 =
              let uu____2575 = FStar_Syntax_Subst.compress ty in
              uu____2575.FStar_Syntax_Syntax.n in
            match uu____2574 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2590 =
                  let uu____2591 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2591 in
                if uu____2590
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2605 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2605 s in
                       let uu____2607 =
                         let uu____2608 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2608 in
                       if uu____2607
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2611 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2611 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2622  ->
                                  match uu____2622 with
                                  | (bv,uu____2628) ->
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
            | uu____2643 ->
                ((let uu____2645 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2645);
                 false) in
          let rec is_valid_application head2 =
            let uu____2650 =
              let uu____2651 = FStar_Syntax_Subst.compress head2 in
              uu____2651.FStar_Syntax_Syntax.n in
            match uu____2650 with
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
                  (let uu____2655 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2655)
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
                 let uu___108_2772 = env in
                 let uu____2773 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2773;
                   subst = (uu___108_2772.subst);
                   tc_const = (uu___108_2772.tc_const)
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
               ((let uu___109_2790 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_2790.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_2790.FStar_Syntax_Syntax.index);
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
let is_monadic uu___93_3019 =
  match uu___93_3019 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3031;
        FStar_Syntax_Syntax.res_typ = uu____3032;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3034;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3051  ->
              match uu___92_3051 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3052 -> false))
  | Some (FStar_Util.Inr (uu____3053,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3066  ->
              match uu___92_3066 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3067 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3072 =
      let uu____3073 = FStar_Syntax_Subst.compress t in
      uu____3073.FStar_Syntax_Syntax.n in
    match uu____3072 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3093 =
            let uu____3094 = FStar_List.hd args in fst uu____3094 in
          is_C uu____3093 in
        if r
        then
          ((let uu____3106 =
              let uu____3107 =
                FStar_List.for_all
                  (fun uu____3110  ->
                     match uu____3110 with | (h,uu____3114) -> is_C h) args in
              Prims.op_Negation uu____3107 in
            if uu____3106 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3118 =
              let uu____3119 =
                FStar_List.for_all
                  (fun uu____3122  ->
                     match uu____3122 with
                     | (h,uu____3126) ->
                         let uu____3127 = is_C h in
                         Prims.op_Negation uu____3127) args in
              Prims.op_Negation uu____3119 in
            if uu____3118 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3141 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3141 with
         | M t1 ->
             ((let uu____3144 = is_C t1 in
               if uu____3144 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3148) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3154) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3160,uu____3161) -> is_C t1
    | uu____3190 -> false
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
  fun uu___94_3277  ->
    match uu___94_3277 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3278 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3412 =
          match uu____3412 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3433 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3434 =
                       let uu____3435 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3435 in
                     Prims.op_Negation uu____3434) in
                if uu____3433
                then
                  let uu____3436 =
                    let uu____3437 =
                      let uu____3438 = FStar_Syntax_Print.term_to_string e in
                      let uu____3439 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3440 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3438 uu____3439 uu____3440 in
                    FStar_Errors.Err uu____3437 in
                  raise uu____3436
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3454 = mk_return env t1 s_e in
                     ((M t1), uu____3454, u_e)))
               | (M t1,N t2) ->
                   let uu____3457 =
                     let uu____3458 =
                       let uu____3459 = FStar_Syntax_Print.term_to_string e in
                       let uu____3460 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3461 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3459 uu____3460 uu____3461 in
                     FStar_Errors.Err uu____3458 in
                   raise uu____3457) in
        let ensure_m env1 e2 =
          let strip_m uu___95_3487 =
            match uu___95_3487 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3497 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3508 =
                let uu____3509 =
                  let uu____3512 =
                    let uu____3513 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3513 in
                  (uu____3512, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3509 in
              raise uu____3508
          | M uu____3517 ->
              let uu____3518 = check env1 e2 context_nm in strip_m uu____3518 in
        let uu____3522 =
          let uu____3523 = FStar_Syntax_Subst.compress e in
          uu____3523.FStar_Syntax_Syntax.n in
        match uu____3522 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3529 ->
            let uu____3530 = infer env e in return_if uu____3530
        | FStar_Syntax_Syntax.Tm_name uu____3534 ->
            let uu____3535 = infer env e in return_if uu____3535
        | FStar_Syntax_Syntax.Tm_fvar uu____3539 ->
            let uu____3540 = infer env e in return_if uu____3540
        | FStar_Syntax_Syntax.Tm_abs uu____3544 ->
            let uu____3559 = infer env e in return_if uu____3559
        | FStar_Syntax_Syntax.Tm_constant uu____3563 ->
            let uu____3564 = infer env e in return_if uu____3564
        | FStar_Syntax_Syntax.Tm_app uu____3568 ->
            let uu____3578 = infer env e in return_if uu____3578
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3625) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3631) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3637,uu____3638) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3667 ->
            let uu____3675 =
              let uu____3676 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3676 in
            failwith uu____3675
        | FStar_Syntax_Syntax.Tm_type uu____3680 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3684 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3695 ->
            let uu____3700 =
              let uu____3701 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3701 in
            failwith uu____3700
        | FStar_Syntax_Syntax.Tm_uvar uu____3705 ->
            let uu____3714 =
              let uu____3715 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3715 in
            failwith uu____3714
        | FStar_Syntax_Syntax.Tm_delayed uu____3719 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3743 =
              let uu____3744 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3744 in
            failwith uu____3743
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
      let uu____3766 =
        let uu____3767 = FStar_Syntax_Subst.compress e in
        uu____3767.FStar_Syntax_Syntax.n in
      match uu____3766 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___110_3807 = env in
            let uu____3808 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3808;
              subst = (uu___110_3807.subst);
              tc_const = (uu___110_3807.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3817  ->
                 match uu____3817 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___111_3825 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___111_3825.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___111_3825.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3826 =
            FStar_List.fold_left
              (fun uu____3835  ->
                 fun uu____3836  ->
                   match (uu____3835, uu____3836) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3864 = is_C c in
                       if uu____3864
                       then
                         let xw =
                           let uu____3869 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3869 in
                         let x =
                           let uu___112_3871 = bv in
                           let uu____3872 =
                             let uu____3875 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3875 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___112_3871.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___112_3871.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3872
                           } in
                         let env3 =
                           let uu___113_3877 = env2 in
                           let uu____3878 =
                             let uu____3880 =
                               let uu____3881 =
                                 let uu____3886 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3886) in
                               FStar_Syntax_Syntax.NT uu____3881 in
                             uu____3880 :: (env2.subst) in
                           {
                             env = (uu___113_3877.env);
                             subst = uu____3878;
                             tc_const = (uu___113_3877.tc_const)
                           } in
                         let uu____3887 =
                           let uu____3889 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3890 =
                             let uu____3892 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3892 :: acc in
                           uu____3889 :: uu____3890 in
                         (env3, uu____3887)
                       else
                         (let x =
                            let uu___114_3896 = bv in
                            let uu____3897 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_3896.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_3896.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3897
                            } in
                          let uu____3900 =
                            let uu____3902 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3902 :: acc in
                          (env2, uu____3900))) (env1, []) binders1 in
          (match uu____3826 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3914 =
                 let check_what =
                   let uu____3926 = is_monadic what in
                   if uu____3926 then check_m else check_n in
                 let uu____3935 = check_what env2 body1 in
                 match uu____3935 with
                 | (t,s_body,u_body) ->
                     let uu____3945 =
                       let uu____3946 =
                         let uu____3947 = is_monadic what in
                         if uu____3947 then M t else N t in
                       comp_of_nm uu____3946 in
                     (uu____3945, s_body, u_body) in
               (match uu____3914 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3990 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___96_3992  ->
                                    match uu___96_3992 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3993 -> false)) in
                          if uu____3990
                          then
                            let double_starred_comp =
                              let uu____4001 =
                                let uu____4002 =
                                  let uu____4003 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____4003 in
                                FStar_All.pipe_left double_star uu____4002 in
                              FStar_Syntax_Syntax.mk_Total uu____4001 in
                            let flags =
                              FStar_List.filter
                                (fun uu___97_4008  ->
                                   match uu___97_4008 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____4009 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____4010 =
                              let uu____4016 =
                                let uu____4017 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____4017 in
                              FStar_Util.Inl uu____4016 in
                            Some uu____4010
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___115_4037 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___115_4037.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___115_4037.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___115_4037.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4038  ->
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
                          let uu____4055 =
                            let uu____4061 =
                              let uu____4065 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___98_4067  ->
                                        match uu___98_4067 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4068 -> false)) in
                              if uu____4065
                              then
                                let uu____4072 =
                                  FStar_List.filter
                                    (fun uu___99_4074  ->
                                       match uu___99_4074 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4075 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4072)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4061 in
                          Some uu____4055 in
                    let uu____4087 =
                      let comp1 =
                        let uu____4099 = is_monadic what in
                        let uu____4100 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4099 uu____4100 in
                      let uu____4101 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4101,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4087 with
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
                FStar_Syntax_Syntax.ty = uu____4179;
                FStar_Syntax_Syntax.p = uu____4180;_};
            FStar_Syntax_Syntax.fv_delta = uu____4181;
            FStar_Syntax_Syntax.fv_qual = uu____4182;_}
          ->
          let uu____4188 =
            let uu____4191 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4191 in
          (match uu____4188 with
           | (uu____4207,t) ->
               let uu____4209 = let uu____4210 = normalize1 t in N uu____4210 in
               (uu____4209, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4227 = check_n env head1 in
          (match uu____4227 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4241 =
                   let uu____4242 = FStar_Syntax_Subst.compress t in
                   uu____4242.FStar_Syntax_Syntax.n in
                 match uu____4241 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4245 -> true
                 | uu____4253 -> false in
               let rec flatten1 t =
                 let uu____4265 =
                   let uu____4266 = FStar_Syntax_Subst.compress t in
                   uu____4266.FStar_Syntax_Syntax.n in
                 match uu____4265 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4278);
                                FStar_Syntax_Syntax.tk = uu____4279;
                                FStar_Syntax_Syntax.pos = uu____4280;
                                FStar_Syntax_Syntax.vars = uu____4281;_})
                     when is_arrow t1 ->
                     let uu____4298 = flatten1 t1 in
                     (match uu____4298 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4350,uu____4351)
                     -> flatten1 e1
                 | uu____4380 ->
                     let uu____4381 =
                       let uu____4382 =
                         let uu____4383 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4383 in
                       FStar_Errors.Err uu____4382 in
                     raise uu____4381 in
               let uu____4391 = flatten1 t_head in
               (match uu____4391 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4443 =
                          let uu____4444 =
                            let uu____4445 = FStar_Util.string_of_int n1 in
                            let uu____4452 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4463 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4445 uu____4452 uu____4463 in
                          FStar_Errors.Err uu____4444 in
                        raise uu____4443)
                     else ();
                     (let uu____4471 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____4471 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4498 args1 =
                            match uu____4498 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4541 =
                                       let uu____4542 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____4542.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____4541
                                 | (binders3,[]) ->
                                     let uu____4561 =
                                       let uu____4562 =
                                         let uu____4565 =
                                           let uu____4566 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4566 in
                                         FStar_Syntax_Subst.compress
                                           uu____4565 in
                                       uu____4562.FStar_Syntax_Syntax.n in
                                     (match uu____4561 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4582 =
                                            let uu____4583 =
                                              let uu____4584 =
                                                let uu____4592 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____4592) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4584 in
                                            mk1 uu____4583 in
                                          N uu____4582
                                      | uu____4596 -> failwith "wat?")
                                 | ([],uu____4597::uu____4598) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4623)::binders3,(arg,uu____4626)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____4660 = FStar_List.splitAt n' binders1 in
                          (match uu____4660 with
                           | (binders2,uu____4679) ->
                               let uu____4692 =
                                 let uu____4702 =
                                   FStar_List.map2
                                     (fun uu____4722  ->
                                        fun uu____4723  ->
                                          match (uu____4722, uu____4723) with
                                          | ((bv,uu____4740),(arg,q)) ->
                                              let uu____4747 =
                                                let uu____4748 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4748.FStar_Syntax_Syntax.n in
                                              (match uu____4747 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4758 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4771 ->
                                                   let uu____4772 =
                                                     check_n env arg in
                                                   (match uu____4772 with
                                                    | (uu____4783,s_arg,u_arg)
                                                        ->
                                                        let uu____4786 =
                                                          let uu____4790 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4790
                                                          then
                                                            let uu____4794 =
                                                              let uu____4797
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4797, q) in
                                                            [uu____4794;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4786))))
                                     binders2 args in
                                 FStar_List.split uu____4702 in
                               (match uu____4692 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4844 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4850 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4844, uu____4850)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4899) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4905) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4911,uu____4912) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4942 = let uu____4943 = env.tc_const c in N uu____4943 in
          (uu____4942, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4944 ->
          let uu____4952 =
            let uu____4953 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4953 in
          failwith uu____4952
      | FStar_Syntax_Syntax.Tm_type uu____4957 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4961 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4972 ->
          let uu____4977 =
            let uu____4978 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4978 in
          failwith uu____4977
      | FStar_Syntax_Syntax.Tm_uvar uu____4982 ->
          let uu____4991 =
            let uu____4992 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4992 in
          failwith uu____4991
      | FStar_Syntax_Syntax.Tm_delayed uu____4996 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5020 =
            let uu____5021 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____5021 in
          failwith uu____5020
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
          let uu____5059 = check_n env e0 in
          match uu____5059 with
          | (uu____5066,s_e0,u_e0) ->
              let uu____5069 =
                let uu____5087 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5120 = FStar_Syntax_Subst.open_branch b in
                       match uu____5120 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___116_5152 = env in
                             let uu____5153 =
                               let uu____5154 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5154 in
                             {
                               env = uu____5153;
                               subst = (uu___116_5152.subst);
                               tc_const = (uu___116_5152.tc_const)
                             } in
                           let uu____5156 = f env1 body in
                           (match uu____5156 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5205 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5087 in
              (match uu____5069 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5270 = FStar_List.hd nms in
                     match uu____5270 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_5274  ->
                          match uu___100_5274 with
                          | M uu____5275 -> true
                          | uu____5276 -> false) nms in
                   let uu____5277 =
                     let uu____5300 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5352  ->
                              match uu____5352 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5475 =
                                         check env original_body (M t2) in
                                       (match uu____5475 with
                                        | (uu____5498,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5527,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5300 in
                   (match uu____5277 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5646  ->
                                 match uu____5646 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5687 =
                                         let uu____5688 =
                                           let uu____5698 =
                                             let uu____5702 =
                                               let uu____5705 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5706 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5705, uu____5706) in
                                             [uu____5702] in
                                           (s_body, uu____5698) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5688 in
                                       mk1 uu____5687 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5728 =
                              let uu____5729 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5729] in
                            let uu____5730 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5732 =
                              let uu____5739 =
                                let uu____5745 =
                                  let uu____5746 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5746 in
                                FStar_Util.Inl uu____5745 in
                              Some uu____5739 in
                            FStar_Syntax_Util.abs uu____5728 uu____5730
                              uu____5732 in
                          let t1_star =
                            let uu____5760 =
                              let uu____5764 =
                                let uu____5765 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5765 in
                              [uu____5764] in
                            let uu____5766 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5760 uu____5766 in
                          let uu____5769 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5799 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5769, uu____5799)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5813 =
                             let uu____5816 =
                               let uu____5817 =
                                 let uu____5835 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5835,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5817 in
                             mk1 uu____5816 in
                           let uu____5862 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5813, uu____5862))))
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
              let uu____5905 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5905] in
            let uu____5906 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5906 with
            | (x_binders1,e21) ->
                let uu____5914 = infer env e1 in
                (match uu____5914 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5925 = is_C t1 in
                       if uu____5925
                       then
                         let uu___117_5926 = binding in
                         let uu____5927 =
                           let uu____5930 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5930 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___117_5926.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___117_5926.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5927;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___117_5926.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___117_5926.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___118_5933 = env in
                       let uu____5934 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5935 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5935.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5935.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5934;
                         subst = (uu___118_5933.subst);
                         tc_const = (uu___118_5933.tc_const)
                       } in
                     let uu____5936 = proceed env1 e21 in
                     (match uu____5936 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___120_5947 = binding in
                            let uu____5948 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_5947.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___120_5947.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5948;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_5947.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___120_5947.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5951 =
                            let uu____5954 =
                              let uu____5955 =
                                let uu____5963 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___121_5968 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5968.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5968.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5968.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5968.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5963) in
                              FStar_Syntax_Syntax.Tm_let uu____5955 in
                            mk1 uu____5954 in
                          let uu____5969 =
                            let uu____5972 =
                              let uu____5973 =
                                let uu____5981 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___122_5986 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_5986.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_5986.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_5986.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_5986.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5981) in
                              FStar_Syntax_Syntax.Tm_let uu____5973 in
                            mk1 uu____5972 in
                          (nm_rec, uu____5951, uu____5969))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___123_5995 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___123_5995.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___123_5995.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___123_5995.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___124_5997 = env in
                       let uu____5998 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_5999 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_5999.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_5999.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5998;
                         subst = (uu___124_5997.subst);
                         tc_const = (uu___124_5997.tc_const)
                       } in
                     let uu____6000 = ensure_m env1 e21 in
                     (match uu____6000 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____6017 =
                              let uu____6018 =
                                let uu____6028 =
                                  let uu____6032 =
                                    let uu____6035 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6036 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6035, uu____6036) in
                                  [uu____6032] in
                                (s_e2, uu____6028) in
                              FStar_Syntax_Syntax.Tm_app uu____6018 in
                            mk1 uu____6017 in
                          let s_e22 =
                            let uu____6045 =
                              let uu____6052 =
                                let uu____6058 =
                                  let uu____6059 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6059 in
                                FStar_Util.Inl uu____6058 in
                              Some uu____6052 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6045 in
                          let body =
                            let uu____6073 =
                              let uu____6074 =
                                let uu____6084 =
                                  let uu____6088 =
                                    let uu____6091 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6091) in
                                  [uu____6088] in
                                (s_e1, uu____6084) in
                              FStar_Syntax_Syntax.Tm_app uu____6074 in
                            mk1 uu____6073 in
                          let uu____6099 =
                            let uu____6100 =
                              let uu____6101 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6101] in
                            let uu____6102 =
                              let uu____6109 =
                                let uu____6115 =
                                  let uu____6116 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6116 in
                                FStar_Util.Inl uu____6115 in
                              Some uu____6109 in
                            FStar_Syntax_Util.abs uu____6100 body uu____6102 in
                          let uu____6127 =
                            let uu____6130 =
                              let uu____6131 =
                                let uu____6139 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___126_6144 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_6144.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_6144.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_6144.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_6144.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6139) in
                              FStar_Syntax_Syntax.Tm_let uu____6131 in
                            mk1 uu____6130 in
                          ((M t2), uu____6099, uu____6127)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6153 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6153 in
      let uu____6158 = check env e mn in
      match uu____6158 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6168 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6181 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        M uu____6181 in
      let uu____6186 = check env e mn in
      match uu____6186 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6196 -> failwith "[check_m]: impossible"
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
        (let uu____6218 =
           let uu____6219 = is_C c in Prims.op_Negation uu____6219 in
         if uu____6218 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6231 =
           let uu____6232 = FStar_Syntax_Subst.compress c in
           uu____6232.FStar_Syntax_Syntax.n in
         match uu____6231 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6251 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6251 with
              | (wp_head,wp_args) ->
                  ((let uu____6278 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6295 =
                           let uu____6296 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6296 in
                         Prims.op_Negation uu____6295) in
                    if uu____6278 then failwith "mismatch" else ());
                   (let uu____6308 =
                      let uu____6309 =
                        let uu____6319 =
                          FStar_List.map2
                            (fun uu____6329  ->
                               fun uu____6330  ->
                                 match (uu____6329, uu____6330) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6353 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6353
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6356 = print_implicit q in
                                         let uu____6357 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6356 uu____6357)
                                      else ();
                                      (let uu____6359 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6359, q)))) args wp_args in
                        (head1, uu____6319) in
                      FStar_Syntax_Syntax.Tm_app uu____6309 in
                    mk1 uu____6308)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6381 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6381 with
              | (binders_orig,comp1) ->
                  let uu____6386 =
                    let uu____6394 =
                      FStar_List.map
                        (fun uu____6408  ->
                           match uu____6408 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6421 = is_C h in
                               if uu____6421
                               then
                                 let w' =
                                   let uu____6428 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6428 in
                                 let uu____6429 =
                                   let uu____6433 =
                                     let uu____6437 =
                                       let uu____6440 =
                                         let uu____6441 =
                                           let uu____6442 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6442 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6441 in
                                       (uu____6440, q) in
                                     [uu____6437] in
                                   (w', q) :: uu____6433 in
                                 (w', uu____6429)
                               else
                                 (let x =
                                    let uu____6454 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6454 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6394 in
                  (match uu____6386 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6484 =
                           let uu____6486 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6486 in
                         FStar_Syntax_Subst.subst_comp uu____6484 comp1 in
                       let app =
                         let uu____6490 =
                           let uu____6491 =
                             let uu____6501 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6508 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6509 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6508, uu____6509)) bvs in
                             (wp, uu____6501) in
                           FStar_Syntax_Syntax.Tm_app uu____6491 in
                         mk1 uu____6490 in
                       let comp3 =
                         let uu____6514 = type_of_comp comp2 in
                         let uu____6515 = is_monadic_comp comp2 in
                         trans_G env uu____6514 uu____6515 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6517,uu____6518) ->
             trans_F_ env e wp
         | uu____6547 -> failwith "impossible trans_F_")
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
            let uu____6552 =
              let uu____6553 = star_type' env h in
              let uu____6556 =
                let uu____6562 =
                  let uu____6565 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6565) in
                [uu____6562] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6553;
                FStar_Syntax_Syntax.effect_args = uu____6556;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6552
          else
            (let uu____6571 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6571)
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
    fun t  -> let uu____6586 = n env.env t in star_type' env uu____6586
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6600 = n env.env t in check_n env uu____6600
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6613 = n env.env c in
        let uu____6614 = n env.env wp in trans_F_ env uu____6613 uu____6614