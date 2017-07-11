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
            (let uu____102 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____102
             then
               (d "Elaborating extra WP combinators";
                (let uu____104 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____104))
             else ());
            (let rec collect_binders t =
               let uu____113 =
                 let uu____114 =
                   let uu____116 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____116 in
                 uu____114.FStar_Syntax_Syntax.n in
               match uu____113 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____134) -> t1
                     | uu____139 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____141 = collect_binders rest in
                   FStar_List.append bs uu____141
               | FStar_Syntax_Syntax.Tm_type uu____147 -> []
               | uu____150 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____162 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____162 FStar_Syntax_Util.name_binders in
             (let uu____173 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____173
              then
                let uu____174 =
                  let uu____175 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____175 in
                d uu____174
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env1 lident def =
                let uu____201 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def in
                match uu____201 with
                | (sigelt,fv) ->
                    ((let uu____207 =
                        let uu____209 = FStar_ST.read sigelts in sigelt ::
                          uu____209 in
                      FStar_ST.write sigelts uu____207);
                     fv) in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____234  ->
                     match uu____234 with
                     | (t,b) ->
                         let uu____241 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____241)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____260 = FStar_Syntax_Syntax.as_implicit true in
                     ((FStar_Pervasives_Native.fst t), uu____260)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____275 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____275) in
              let uu____276 =
                let uu____286 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu____303 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____303 in
                    let uu____305 =
                      let uu____306 =
                        let uu____310 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____311 =
                          let uu____313 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____313] in
                        uu____310 :: uu____311 in
                      FStar_List.append binders uu____306 in
                    FStar_Syntax_Util.abs uu____305 body
                      FStar_Pervasives_Native.None in
                  let uu____316 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____317 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____316, uu____317) in
                match uu____286 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____343 =
                        let uu____344 =
                          let uu____352 =
                            let uu____356 =
                              FStar_List.map
                                (fun uu____369  ->
                                   match uu____369 with
                                   | (bv,uu____375) ->
                                       let uu____376 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____377 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____376, uu____377)) binders in
                            let uu____378 =
                              let uu____382 =
                                let uu____385 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____386 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____385, uu____386) in
                              let uu____387 =
                                let uu____391 =
                                  let uu____394 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____394) in
                                [uu____391] in
                              uu____382 :: uu____387 in
                            FStar_List.append uu____356 uu____378 in
                          (fv, uu____352) in
                        FStar_Syntax_Syntax.Tm_app uu____344 in
                      mk1 uu____343 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____276 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu____433 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____433 in
                    let ret1 =
                      let uu____436 =
                        let uu____437 =
                          let uu____439 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu____439 in
                        FStar_Syntax_Util.residual_tot uu____437 in
                      FStar_Pervasives_Native.Some uu____436 in
                    let body =
                      let uu____441 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____441 ret1 in
                    let uu____442 =
                      let uu____443 = mk_all_implicit binders in
                      let uu____447 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____443 uu____447 in
                    FStar_Syntax_Util.abs uu____442 body ret1 in
                  let c_pure1 =
                    let uu____462 = mk_lid "pure" in
                    register env1 uu____462 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu____467 =
                        let uu____468 =
                          let uu____469 =
                            let uu____473 =
                              let uu____474 =
                                let uu____475 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____475 in
                              FStar_Syntax_Syntax.mk_binder uu____474 in
                            [uu____473] in
                          let uu____476 =
                            let uu____478 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____478 in
                          FStar_Syntax_Util.arrow uu____469 uu____476 in
                        mk_gctx uu____468 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____467 in
                    let r =
                      let uu____480 =
                        let uu____481 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____481 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____480 in
                    let ret1 =
                      let uu____484 =
                        let uu____485 =
                          let uu____487 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____487 in
                        FStar_Syntax_Util.residual_tot uu____485 in
                      FStar_Pervasives_Native.Some uu____484 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____493 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____495 =
                          let uu____500 =
                            let uu____502 =
                              let uu____503 =
                                let uu____504 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____504
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____503 in
                            [uu____502] in
                          FStar_List.append gamma_as_args uu____500 in
                        FStar_Syntax_Util.mk_app uu____493 uu____495 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____506 =
                      let uu____507 = mk_all_implicit binders in
                      let uu____511 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____507 uu____511 in
                    FStar_Syntax_Util.abs uu____506 outer_body ret1 in
                  let c_app1 =
                    let uu____530 = mk_lid "app" in
                    register env1 uu____530 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____536 =
                        let uu____540 =
                          let uu____541 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____541 in
                        [uu____540] in
                      let uu____542 =
                        let uu____544 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____544 in
                      FStar_Syntax_Util.arrow uu____536 uu____542 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____547 =
                        let uu____548 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____548 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____547 in
                    let ret1 =
                      let uu____551 =
                        let uu____552 =
                          let uu____554 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____554 in
                        FStar_Syntax_Util.residual_tot uu____552 in
                      FStar_Pervasives_Native.Some uu____551 in
                    let uu____555 =
                      let uu____556 = mk_all_implicit binders in
                      let uu____560 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____556 uu____560 in
                    let uu____578 =
                      let uu____579 =
                        let uu____584 =
                          let uu____586 =
                            let uu____588 =
                              let uu____593 =
                                let uu____595 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____595] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____593 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____588 in
                          let uu____596 =
                            let uu____599 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____599] in
                          uu____586 :: uu____596 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____584 in
                      FStar_Syntax_Util.mk_app c_app1 uu____579 in
                    FStar_Syntax_Util.abs uu____555 uu____578 ret1 in
                  let c_lift11 =
                    let uu____602 = mk_lid "lift1" in
                    register env1 uu____602 c_lift1 in
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
                      let uu____609 =
                        let uu____613 =
                          let uu____614 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____614 in
                        let uu____615 =
                          let uu____617 =
                            let uu____618 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____618 in
                          [uu____617] in
                        uu____613 :: uu____615 in
                      let uu____619 =
                        let uu____621 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____621 in
                      FStar_Syntax_Util.arrow uu____609 uu____619 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu____624 =
                        let uu____625 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____625 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____624 in
                    let a2 =
                      let uu____627 =
                        let uu____628 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____628 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____627 in
                    let ret1 =
                      let uu____631 =
                        let uu____632 =
                          let uu____634 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu____634 in
                        FStar_Syntax_Util.residual_tot uu____632 in
                      FStar_Pervasives_Native.Some uu____631 in
                    let uu____635 =
                      let uu____636 = mk_all_implicit binders in
                      let uu____640 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu____636 uu____640 in
                    let uu____662 =
                      let uu____663 =
                        let uu____668 =
                          let uu____670 =
                            let uu____672 =
                              let uu____677 =
                                let uu____679 =
                                  let uu____681 =
                                    let uu____686 =
                                      let uu____688 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu____688] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____686 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____681 in
                                let uu____689 =
                                  let uu____692 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu____692] in
                                uu____679 :: uu____689 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____677 in
                            FStar_Syntax_Util.mk_app c_app1 uu____672 in
                          let uu____694 =
                            let uu____697 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu____697] in
                          uu____670 :: uu____694 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____668 in
                      FStar_Syntax_Util.mk_app c_app1 uu____663 in
                    FStar_Syntax_Util.abs uu____635 uu____662 ret1 in
                  let c_lift21 =
                    let uu____700 = mk_lid "lift2" in
                    register env1 uu____700 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____706 =
                        let uu____710 =
                          let uu____711 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____711 in
                        [uu____710] in
                      let uu____712 =
                        let uu____714 =
                          let uu____715 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu____715 in
                        FStar_Syntax_Syntax.mk_Total uu____714 in
                      FStar_Syntax_Util.arrow uu____706 uu____712 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret1 =
                      let uu____719 =
                        let uu____720 =
                          let uu____722 =
                            let uu____723 =
                              let uu____727 =
                                let uu____728 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu____728 in
                              [uu____727] in
                            let uu____729 =
                              let uu____731 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu____731 in
                            FStar_Syntax_Util.arrow uu____723 uu____729 in
                          mk_ctx uu____722 in
                        FStar_Syntax_Util.residual_tot uu____720 in
                      FStar_Pervasives_Native.Some uu____719 in
                    let e1 =
                      let uu____733 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____733 in
                    let body =
                      let uu____735 =
                        let uu____736 =
                          let uu____740 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____740] in
                        FStar_List.append gamma uu____736 in
                      let uu____743 =
                        let uu____744 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____746 =
                          let uu____751 =
                            let uu____752 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____752 in
                          let uu____753 = args_of_binders1 gamma in uu____751
                            :: uu____753 in
                        FStar_Syntax_Util.mk_app uu____744 uu____746 in
                      FStar_Syntax_Util.abs uu____735 uu____743 ret1 in
                    let uu____755 =
                      let uu____756 = mk_all_implicit binders in
                      let uu____760 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____756 uu____760 in
                    FStar_Syntax_Util.abs uu____755 body ret1 in
                  let c_push1 =
                    let uu____777 = mk_lid "push" in
                    register env1 uu____777 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____796 =
                        let uu____797 =
                          let uu____805 = args_of_binders1 binders in
                          (c, uu____805) in
                        FStar_Syntax_Syntax.Tm_app uu____797 in
                      mk1 uu____796
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____812 =
                        let uu____813 =
                          let uu____817 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____818 =
                            let uu____820 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____820] in
                          uu____817 :: uu____818 in
                        let uu____821 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____813 uu____821 in
                      FStar_Syntax_Syntax.mk_Total uu____812 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu____824 =
                      let uu____825 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____825 in
                    let uu____831 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None in
                      let uu____833 =
                        let uu____835 =
                          let uu____840 =
                            let uu____842 =
                              let uu____844 =
                                let uu____849 =
                                  let uu____850 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____850 in
                                [uu____849] in
                              FStar_Syntax_Util.mk_app l_ite uu____844 in
                            [uu____842] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg uu____840 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____835 in
                      FStar_Syntax_Util.ascribe uu____833
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu____824 uu____831
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu____861 = mk_lid "wp_if_then_else" in
                    register env1 uu____861 wp_if_then_else in
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
                      let uu____870 =
                        let uu____875 =
                          let uu____877 =
                            let uu____879 =
                              let uu____884 =
                                let uu____886 =
                                  let uu____888 =
                                    let uu____893 =
                                      let uu____894 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____894 in
                                    [uu____893] in
                                  FStar_Syntax_Util.mk_app l_and uu____888 in
                                [uu____886] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____884 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____879 in
                          let uu____897 =
                            let uu____900 = FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____900] in
                          uu____877 :: uu____897 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____875 in
                      FStar_Syntax_Util.mk_app c_app1 uu____870 in
                    let uu____902 =
                      let uu____903 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____903 in
                    FStar_Syntax_Util.abs uu____902 body ret_tot_wp_a in
                  let wp_assert1 =
                    let uu____910 = mk_lid "wp_assert" in
                    register env1 uu____910 wp_assert in
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
                      let uu____919 =
                        let uu____924 =
                          let uu____926 =
                            let uu____928 =
                              let uu____933 =
                                let uu____935 =
                                  let uu____937 =
                                    let uu____942 =
                                      let uu____943 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____943 in
                                    [uu____942] in
                                  FStar_Syntax_Util.mk_app l_imp uu____937 in
                                [uu____935] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____933 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____928 in
                          let uu____946 =
                            let uu____949 = FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____949] in
                          uu____926 :: uu____946 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____924 in
                      FStar_Syntax_Util.mk_app c_app1 uu____919 in
                    let uu____951 =
                      let uu____952 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____952 in
                    FStar_Syntax_Util.abs uu____951 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____959 = mk_lid "wp_assume" in
                    register env1 uu____959 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____966 =
                        let uu____970 =
                          let uu____971 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____971 in
                        [uu____970] in
                      let uu____972 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____966 uu____972 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu____977 =
                        let uu____982 =
                          let uu____984 =
                            let uu____986 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____986 in
                          let uu____991 =
                            let uu____994 =
                              let uu____996 =
                                let uu____1001 =
                                  let uu____1003 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1003] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1001 in
                              FStar_Syntax_Util.mk_app c_push1 uu____996 in
                            [uu____994] in
                          uu____984 :: uu____991 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____982 in
                      FStar_Syntax_Util.mk_app c_app1 uu____977 in
                    let uu____1007 =
                      let uu____1008 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1008 in
                    FStar_Syntax_Util.abs uu____1007 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1015 = mk_lid "wp_close" in
                    register env1 uu____1015 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu____1022 =
                      let uu____1023 =
                        let uu____1024 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1024 in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1023 in
                    FStar_Pervasives_Native.Some uu____1022 in
                  let mk_forall1 x body =
                    let uu____1034 =
                      let uu____1036 =
                        let uu____1037 =
                          let uu____1045 =
                            let uu____1047 =
                              let uu____1048 =
                                let uu____1049 =
                                  let uu____1050 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1050] in
                                FStar_Syntax_Util.abs uu____1049 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1048 in
                            [uu____1047] in
                          (FStar_Syntax_Util.tforall, uu____1045) in
                        FStar_Syntax_Syntax.Tm_app uu____1037 in
                      FStar_Syntax_Syntax.mk uu____1036 in
                    uu____1034 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1062 =
                      let uu____1063 = FStar_Syntax_Subst.compress t in
                      uu____1063.FStar_Syntax_Syntax.n in
                    match uu____1062 with
                    | FStar_Syntax_Syntax.Tm_type uu____1065 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1081  ->
                              match uu____1081 with
                              | (b,uu____1085) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1086 -> true in
                  let rec is_monotonic t =
                    let uu____1091 =
                      let uu____1092 = FStar_Syntax_Subst.compress t in
                      uu____1092.FStar_Syntax_Syntax.n in
                    match uu____1091 with
                    | FStar_Syntax_Syntax.Tm_type uu____1094 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1110  ->
                              match uu____1110 with
                              | (b,uu____1114) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1115 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1157 =
                      let uu____1158 = FStar_Syntax_Subst.compress t1 in
                      uu____1158.FStar_Syntax_Syntax.n in
                    match uu____1157 with
                    | FStar_Syntax_Syntax.Tm_type uu____1160 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1163);
                                      FStar_Syntax_Syntax.pos = uu____1164;
                                      FStar_Syntax_Syntax.vars = uu____1165;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1183 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1183
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1186 =
                              let uu____1188 =
                                let uu____1193 =
                                  let uu____1194 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1194 in
                                [uu____1193] in
                              FStar_Syntax_Util.mk_app x uu____1188 in
                            let uu____1195 =
                              let uu____1197 =
                                let uu____1202 =
                                  let uu____1203 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1203 in
                                [uu____1202] in
                              FStar_Syntax_Util.mk_app y uu____1197 in
                            mk_rel1 b uu____1186 uu____1195 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1208 =
                               let uu____1209 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1211 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1209 uu____1211 in
                             let uu____1213 =
                               let uu____1214 =
                                 let uu____1216 =
                                   let uu____1221 =
                                     let uu____1222 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1222 in
                                   [uu____1221] in
                                 FStar_Syntax_Util.mk_app x uu____1216 in
                               let uu____1223 =
                                 let uu____1225 =
                                   let uu____1230 =
                                     let uu____1231 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1231 in
                                   [uu____1230] in
                                 FStar_Syntax_Util.mk_app y uu____1225 in
                               mk_rel1 b uu____1214 uu____1223 in
                             FStar_Syntax_Util.mk_imp uu____1208 uu____1213 in
                           let uu____1232 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1232)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1235);
                                      FStar_Syntax_Syntax.pos = uu____1236;
                                      FStar_Syntax_Syntax.vars = uu____1237;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1255 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1255
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu____1258 =
                              let uu____1260 =
                                let uu____1265 =
                                  let uu____1266 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1266 in
                                [uu____1265] in
                              FStar_Syntax_Util.mk_app x uu____1260 in
                            let uu____1267 =
                              let uu____1269 =
                                let uu____1274 =
                                  let uu____1275 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1275 in
                                [uu____1274] in
                              FStar_Syntax_Util.mk_app y uu____1269 in
                            mk_rel1 b uu____1258 uu____1267 in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu____1280 =
                               let uu____1281 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1283 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1281 uu____1283 in
                             let uu____1285 =
                               let uu____1286 =
                                 let uu____1288 =
                                   let uu____1293 =
                                     let uu____1294 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1294 in
                                   [uu____1293] in
                                 FStar_Syntax_Util.mk_app x uu____1288 in
                               let uu____1295 =
                                 let uu____1297 =
                                   let uu____1302 =
                                     let uu____1303 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1303 in
                                   [uu____1302] in
                                 FStar_Syntax_Util.mk_app y uu____1297 in
                               mk_rel1 b uu____1286 uu____1295 in
                             FStar_Syntax_Util.mk_imp uu____1280 uu____1285 in
                           let uu____1304 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1304)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___103_1322 = t1 in
                          let uu____1323 =
                            let uu____1324 =
                              let uu____1331 =
                                let uu____1332 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1332 in
                              ([binder], uu____1331) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1324 in
                          {
                            FStar_Syntax_Syntax.n = uu____1323;
                            FStar_Syntax_Syntax.pos =
                              (uu___103_1322.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___103_1322.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1342 ->
                        failwith "unhandled arrow"
                    | uu____1349 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1364 =
                        let uu____1365 = FStar_Syntax_Subst.compress t1 in
                        uu____1365.FStar_Syntax_Syntax.n in
                      match uu____1364 with
                      | FStar_Syntax_Syntax.Tm_type uu____1367 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1380 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1380
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1392 =
                                let uu____1393 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1393 i in
                              FStar_Syntax_Syntax.fvar uu____1392
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu____1413 =
                            let uu____1417 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1428  ->
                                     match uu____1428 with
                                     | (t2,q) ->
                                         let uu____1433 = project i x in
                                         let uu____1434 = project i y in
                                         mk_stronger t2 uu____1433 uu____1434)
                                args in
                            match uu____1417 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1413 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1451);
                                      FStar_Syntax_Syntax.pos = uu____1452;
                                      FStar_Syntax_Syntax.vars = uu____1453;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1476  ->
                                   match uu____1476 with
                                   | (bv,q) ->
                                       let uu____1481 =
                                         let uu____1482 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1482 in
                                       FStar_Syntax_Syntax.gen_bv uu____1481
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1488 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1488) bvs in
                          let body =
                            let uu____1490 = FStar_Syntax_Util.mk_app x args in
                            let uu____1491 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1490 uu____1491 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1498);
                                      FStar_Syntax_Syntax.pos = uu____1499;
                                      FStar_Syntax_Syntax.vars = uu____1500;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1523  ->
                                   match uu____1523 with
                                   | (bv,q) ->
                                       let uu____1528 =
                                         let uu____1529 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1529 in
                                       FStar_Syntax_Syntax.gen_bv uu____1528
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1535 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1535) bvs in
                          let body =
                            let uu____1537 = FStar_Syntax_Util.mk_app x args in
                            let uu____1538 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1537 uu____1538 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1543 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1545 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1546 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1547 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1545 uu____1546 uu____1547 in
                    let uu____1548 =
                      let uu____1549 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1549 in
                    FStar_Syntax_Util.abs uu____1548 body ret_tot_type in
                  let stronger1 =
                    let uu____1564 = mk_lid "stronger" in
                    register env1 uu____1564 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1569 = FStar_Util.prefix gamma in
                    match uu____1569 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1595 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1595 in
                          let uu____1597 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1597 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____1604 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1604 in
                              let guard_free1 =
                                let uu____1610 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1610 in
                              let pat =
                                let uu____1613 =
                                  let uu____1618 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1618] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1613 in
                              let pattern_guarded_body =
                                let uu____1621 =
                                  let uu____1622 =
                                    let uu____1626 =
                                      let uu____1627 =
                                        let uu____1633 =
                                          let uu____1635 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1635] in
                                        [uu____1633] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1627 in
                                    (body, uu____1626) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1622 in
                                mk1 uu____1621 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1638 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1641 =
                            let uu____1642 =
                              let uu____1643 =
                                let uu____1644 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1646 =
                                  let uu____1651 = args_of_binders1 wp_args in
                                  let uu____1653 =
                                    let uu____1655 =
                                      let uu____1656 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1656 in
                                    [uu____1655] in
                                  FStar_List.append uu____1651 uu____1653 in
                                FStar_Syntax_Util.mk_app uu____1644
                                  uu____1646 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1643 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1642 in
                          FStar_Syntax_Util.abs gamma uu____1641
                            ret_gtot_type in
                        let uu____1657 =
                          let uu____1658 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1658 in
                        FStar_Syntax_Util.abs uu____1657 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____1665 = mk_lid "wp_ite" in
                    register env1 uu____1665 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu____1670 = FStar_Util.prefix gamma in
                    match uu____1670 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____1694 =
                            let uu____1695 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post) in
                            let uu____1697 =
                              let uu____1702 =
                                let uu____1703 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____1703 in
                              [uu____1702] in
                            FStar_Syntax_Util.mk_app uu____1695 uu____1697 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1694 in
                        let uu____1704 =
                          let uu____1705 =
                            let uu____1709 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____1709 gamma in
                          FStar_List.append binders uu____1705 in
                        FStar_Syntax_Util.abs uu____1704 body ret_gtot_type in
                  let null_wp1 =
                    let uu____1718 = mk_lid "null_wp" in
                    register env1 uu____1718 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu____1725 =
                        let uu____1730 =
                          let uu____1732 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____1733 =
                            let uu____1735 =
                              let uu____1737 =
                                let uu____1742 =
                                  let uu____1743 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____1743 in
                                [uu____1742] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1737 in
                            let uu____1744 =
                              let uu____1747 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____1747] in
                            uu____1735 :: uu____1744 in
                          uu____1732 :: uu____1733 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1730 in
                      FStar_Syntax_Util.mk_app stronger2 uu____1725 in
                    let uu____1749 =
                      let uu____1750 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____1750 in
                    FStar_Syntax_Util.abs uu____1749 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____1757 = mk_lid "wp_trivial" in
                    register env1 uu____1757 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____1761 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____1761
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____1766 =
                      let uu____1768 = FStar_ST.read sigelts in
                      FStar_List.rev uu____1768 in
                    let uu____1773 =
                      let uu___104_1774 = ed in
                      let uu____1775 =
                        let uu____1776 = c wp_if_then_else2 in
                        ([], uu____1776) in
                      let uu____1778 =
                        let uu____1779 = c wp_ite2 in ([], uu____1779) in
                      let uu____1781 =
                        let uu____1782 = c stronger2 in ([], uu____1782) in
                      let uu____1784 =
                        let uu____1785 = c wp_close2 in ([], uu____1785) in
                      let uu____1787 =
                        let uu____1788 = c wp_assert2 in ([], uu____1788) in
                      let uu____1790 =
                        let uu____1791 = c wp_assume2 in ([], uu____1791) in
                      let uu____1793 =
                        let uu____1794 = c null_wp2 in ([], uu____1794) in
                      let uu____1796 =
                        let uu____1797 = c wp_trivial2 in ([], uu____1797) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___104_1774.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___104_1774.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___104_1774.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___104_1774.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___104_1774.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___104_1774.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___104_1774.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____1775;
                        FStar_Syntax_Syntax.ite_wp = uu____1778;
                        FStar_Syntax_Syntax.stronger = uu____1781;
                        FStar_Syntax_Syntax.close_wp = uu____1784;
                        FStar_Syntax_Syntax.assert_p = uu____1787;
                        FStar_Syntax_Syntax.assume_p = uu____1790;
                        FStar_Syntax_Syntax.null_wp = uu____1793;
                        FStar_Syntax_Syntax.trivial = uu____1796;
                        FStar_Syntax_Syntax.repr =
                          (uu___104_1774.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___104_1774.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___104_1774.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___104_1774.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____1766, uu____1773)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___105_1812 = dmff_env in
      {
        env = env';
        subst = (uu___105_1812.subst);
        tc_const = (uu___105_1812.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____1826 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____1840 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___91_1852  ->
    match uu___91_1852 with
    | FStar_Syntax_Syntax.Total (t,uu____1854) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___90_1862  ->
                match uu___90_1862 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____1863 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____1865 =
          let uu____1866 =
            let uu____1867 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____1867 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____1866 in
        failwith uu____1865
    | FStar_Syntax_Syntax.GTotal uu____1868 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___92_1876  ->
    match uu___92_1876 with
    | N t ->
        let uu____1878 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____1878
    | M t ->
        let uu____1880 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____1880
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____1885,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____1887;
                      FStar_Syntax_Syntax.vars = uu____1888;_})
        -> nm_of_comp n2
    | uu____1897 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp:
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____1904 = nm_of_comp c.FStar_Syntax_Syntax.n in
    match uu____1904 with | M uu____1905 -> true | N uu____1906 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____1911 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____1921 =
        let uu____1925 =
          let uu____1926 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____1926 in
        [uu____1925] in
      let uu____1927 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____1921 uu____1927 in
    let uu____1929 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____1929
let rec mk_star_to_type:
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        mk1
          (let uu____1958 =
             let uu____1965 =
               let uu____1969 =
                 let uu____1972 =
                   let uu____1973 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____1973 in
                 let uu____1974 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____1972, uu____1974) in
               [uu____1969] in
             let uu____1979 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____1965, uu____1979) in
           FStar_Syntax_Syntax.Tm_arrow uu____1958)
and star_type':
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk1 in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2003) ->
          let binders1 =
            FStar_List.map
              (fun uu____2024  ->
                 match uu____2024 with
                 | (bv,aqual) ->
                     let uu____2031 =
                       let uu___106_2032 = bv in
                       let uu____2033 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_2032.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_2032.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2033
                       } in
                     (uu____2031, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2035,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2037);
                             FStar_Syntax_Syntax.pos = uu____2038;
                             FStar_Syntax_Syntax.vars = uu____2039;_})
               ->
               let uu____2052 =
                 let uu____2053 =
                   let uu____2060 =
                     let uu____2061 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2061 in
                   (binders1, uu____2060) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2053 in
               mk1 uu____2052
           | uu____2065 ->
               let uu____2066 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2066 with
                | N hn ->
                    let uu____2068 =
                      let uu____2069 =
                        let uu____2076 =
                          let uu____2077 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2077 in
                        (binders1, uu____2076) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2069 in
                    mk1 uu____2068
                | M a ->
                    let uu____2082 =
                      let uu____2083 =
                        let uu____2090 =
                          let uu____2094 =
                            let uu____2098 =
                              let uu____2101 =
                                let uu____2102 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2102 in
                              let uu____2103 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2101, uu____2103) in
                            [uu____2098] in
                          FStar_List.append binders1 uu____2094 in
                        let uu____2110 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2090, uu____2110) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2083 in
                    mk1 uu____2082))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2157 = f x in
                    FStar_Util.string_builder_append strb uu____2157);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2164 = f x1 in
                         FStar_Util.string_builder_append strb uu____2164))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2166 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2167 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2166 uu____2167 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2175 =
              let uu____2176 = FStar_Syntax_Subst.compress ty in
              uu____2176.FStar_Syntax_Syntax.n in
            match uu____2175 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2188 =
                  let uu____2189 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2189 in
                if uu____2188
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2212 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2212 s in
                       let uu____2214 =
                         let uu____2215 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2215 in
                       if uu____2214
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2218 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2218 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2234  ->
                                  match uu____2234 with
                                  | (bv,uu____2240) ->
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
            | uu____2255 ->
                ((let uu____2257 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2257);
                 false) in
          let rec is_valid_application head2 =
            let uu____2262 =
              let uu____2263 = FStar_Syntax_Subst.compress head2 in
              uu____2263.FStar_Syntax_Syntax.n in
            match uu____2262 with
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
                  (let uu____2267 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2267)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____2269 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu____2269 with
                 | ((uu____2274,ty),uu____2276) ->
                     let uu____2279 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu____2279
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1 in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____2288 -> true
                        | uu____2296 ->
                            ((let uu____2298 =
                                FStar_Syntax_Print.term_to_string head2 in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____2298);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____2300 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2301 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2303) ->
                is_valid_application t2
            | uu____2306 -> false in
          let uu____2307 = is_valid_application head1 in
          if uu____2307
          then
            let uu____2308 =
              let uu____2309 =
                let uu____2317 =
                  FStar_List.map
                    (fun uu____2330  ->
                       match uu____2330 with
                       | (t2,qual) ->
                           let uu____2340 = star_type' env t2 in
                           (uu____2340, qual)) args in
                (head1, uu____2317) in
              FStar_Syntax_Syntax.Tm_app uu____2309 in
            mk1 uu____2308
          else
            (let uu____2346 =
               let uu____2347 =
                 let uu____2348 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2348 in
               FStar_Errors.Err uu____2347 in
             raise uu____2346)
      | FStar_Syntax_Syntax.Tm_bvar uu____2349 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2350 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2351 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2352 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2366 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2366 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___109_2372 = env in
                 let uu____2373 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2373;
                   subst = (uu___109_2372.subst);
                   tc_const = (uu___109_2372.tc_const)
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
               ((let uu___110_2389 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___110_2389.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___110_2389.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2394 =
            let uu____2395 =
              let uu____2399 = star_type' env t2 in (uu____2399, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2395 in
          mk1 uu____2394
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____2425 =
            let uu____2426 =
              let uu____2440 = star_type' env e in
              let uu____2441 =
                let uu____2449 =
                  let uu____2453 = star_type' env t2 in
                  FStar_Util.Inl uu____2453 in
                (uu____2449, FStar_Pervasives_Native.None) in
              (uu____2440, uu____2441, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2426 in
          mk1 uu____2425
      | FStar_Syntax_Syntax.Tm_ascribed uu____2469 ->
          let uu____2483 =
            let uu____2484 =
              let uu____2485 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2485 in
            FStar_Errors.Err uu____2484 in
          raise uu____2483
      | FStar_Syntax_Syntax.Tm_refine uu____2486 ->
          let uu____2490 =
            let uu____2491 =
              let uu____2492 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2492 in
            FStar_Errors.Err uu____2491 in
          raise uu____2490
      | FStar_Syntax_Syntax.Tm_uinst uu____2493 ->
          let uu____2497 =
            let uu____2498 =
              let uu____2499 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2499 in
            FStar_Errors.Err uu____2498 in
          raise uu____2497
      | FStar_Syntax_Syntax.Tm_constant uu____2500 ->
          let uu____2501 =
            let uu____2502 =
              let uu____2503 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2503 in
            FStar_Errors.Err uu____2502 in
          raise uu____2501
      | FStar_Syntax_Syntax.Tm_match uu____2504 ->
          let uu____2516 =
            let uu____2517 =
              let uu____2518 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2518 in
            FStar_Errors.Err uu____2517 in
          raise uu____2516
      | FStar_Syntax_Syntax.Tm_let uu____2519 ->
          let uu____2526 =
            let uu____2527 =
              let uu____2528 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2528 in
            FStar_Errors.Err uu____2527 in
          raise uu____2526
      | FStar_Syntax_Syntax.Tm_uvar uu____2529 ->
          let uu____2538 =
            let uu____2539 =
              let uu____2540 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2540 in
            FStar_Errors.Err uu____2539 in
          raise uu____2538
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2541 =
            let uu____2542 =
              let uu____2543 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2543 in
            FStar_Errors.Err uu____2542 in
          raise uu____2541
      | FStar_Syntax_Syntax.Tm_delayed uu____2544 -> failwith "impossible"
let is_monadic:
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___94_2561  ->
    match uu___94_2561 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___93_2566  ->
                match uu___93_2566 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2567 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2572 =
      let uu____2573 = FStar_Syntax_Subst.compress t in
      uu____2573.FStar_Syntax_Syntax.n in
    match uu____2572 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2588 =
            let uu____2589 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu____2589 in
          is_C uu____2588 in
        if r
        then
          ((let uu____2598 =
              let uu____2599 =
                FStar_List.for_all
                  (fun uu____2605  ->
                     match uu____2605 with | (h,uu____2609) -> is_C h) args in
              Prims.op_Negation uu____2599 in
            if uu____2598 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2613 =
              let uu____2614 =
                FStar_List.for_all
                  (fun uu____2621  ->
                     match uu____2621 with
                     | (h,uu____2625) ->
                         let uu____2626 = is_C h in
                         Prims.op_Negation uu____2626) args in
              Prims.op_Negation uu____2614 in
            if uu____2613 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2638 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____2638 with
         | M t1 ->
             ((let uu____2641 = is_C t1 in
               if uu____2641 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____2645) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2649) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____2653,uu____2654) -> is_C t1
    | uu____2675 -> false
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
          let uu____2701 =
            let uu____2702 =
              let uu____2710 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____2711 =
                let uu____2715 =
                  let uu____2718 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____2718) in
                [uu____2715] in
              (uu____2710, uu____2711) in
            FStar_Syntax_Syntax.Tm_app uu____2702 in
          mk1 uu____2701 in
        let uu____2726 =
          let uu____2727 = FStar_Syntax_Syntax.mk_binder p in [uu____2727] in
        FStar_Syntax_Util.abs uu____2726 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___95_2731  ->
    match uu___95_2731 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____2732 -> false
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
        let return_if uu____2860 =
          match uu____2860 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____2879 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____2881 =
                       let uu____2882 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____2882 in
                     Prims.op_Negation uu____2881) in
                if uu____2879
                then
                  let uu____2883 =
                    let uu____2884 =
                      let uu____2885 = FStar_Syntax_Print.term_to_string e in
                      let uu____2886 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____2887 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____2885 uu____2886 uu____2887 in
                    FStar_Errors.Err uu____2884 in
                  raise uu____2883
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____2901 = mk_return env t1 s_e in
                     ((M t1), uu____2901, u_e)))
               | (M t1,N t2) ->
                   let uu____2904 =
                     let uu____2905 =
                       let uu____2906 = FStar_Syntax_Print.term_to_string e in
                       let uu____2907 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____2908 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____2906 uu____2907 uu____2908 in
                     FStar_Errors.Err uu____2905 in
                   raise uu____2904) in
        let ensure_m env1 e2 =
          let strip_m uu___96_2934 =
            match uu___96_2934 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____2944 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____2955 =
                let uu____2956 =
                  let uu____2959 =
                    let uu____2960 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____2960 in
                  (uu____2959, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____2956 in
              raise uu____2955
          | M uu____2964 ->
              let uu____2965 = check env1 e2 context_nm in strip_m uu____2965 in
        let uu____2969 =
          let uu____2970 = FStar_Syntax_Subst.compress e in
          uu____2970.FStar_Syntax_Syntax.n in
        match uu____2969 with
        | FStar_Syntax_Syntax.Tm_bvar uu____2975 ->
            let uu____2976 = infer env e in return_if uu____2976
        | FStar_Syntax_Syntax.Tm_name uu____2980 ->
            let uu____2981 = infer env e in return_if uu____2981
        | FStar_Syntax_Syntax.Tm_fvar uu____2985 ->
            let uu____2986 = infer env e in return_if uu____2986
        | FStar_Syntax_Syntax.Tm_abs uu____2990 ->
            let uu____2999 = infer env e in return_if uu____2999
        | FStar_Syntax_Syntax.Tm_constant uu____3003 ->
            let uu____3004 = infer env e in return_if uu____3004
        | FStar_Syntax_Syntax.Tm_app uu____3008 ->
            let uu____3016 = infer env e in return_if uu____3016
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3057) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3061) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3065,uu____3066) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3087 ->
            let uu____3094 =
              let uu____3095 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3095 in
            failwith uu____3094
        | FStar_Syntax_Syntax.Tm_type uu____3099 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3103 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3113 ->
            let uu____3117 =
              let uu____3118 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3118 in
            failwith uu____3117
        | FStar_Syntax_Syntax.Tm_uvar uu____3122 ->
            let uu____3131 =
              let uu____3132 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3132 in
            failwith uu____3131
        | FStar_Syntax_Syntax.Tm_delayed uu____3136 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3152 =
              let uu____3153 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3153 in
            failwith uu____3152
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
      let uu____3173 =
        let uu____3174 = FStar_Syntax_Subst.compress e in
        uu____3174.FStar_Syntax_Syntax.n in
      match uu____3173 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____3210;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____3211;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____3215 =
                  let uu___111_3216 = rc in
                  let uu____3217 =
                    let uu____3220 =
                      let uu____3221 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst1 uu____3221 in
                    FStar_Pervasives_Native.Some uu____3220 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___111_3216.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____3217;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___111_3216.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu____3215 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let rc_opt1 = subst_rc_opt subst1 rc_opt in
          let env1 =
            let uu___112_3229 = env in
            let uu____3230 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3230;
              subst = (uu___112_3229.subst);
              tc_const = (uu___112_3229.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3243  ->
                 match uu____3243 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___113_3252 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___113_3252.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___113_3252.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3253 =
            FStar_List.fold_left
              (fun uu____3274  ->
                 fun uu____3275  ->
                   match (uu____3274, uu____3275) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3302 = is_C c in
                       if uu____3302
                       then
                         let xw =
                           let uu____3307 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____3307 in
                         let x =
                           let uu___114_3309 = bv in
                           let uu____3310 =
                             let uu____3312 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3312 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___114_3309.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___114_3309.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3310
                           } in
                         let env3 =
                           let uu___115_3314 = env2 in
                           let uu____3315 =
                             let uu____3317 =
                               let uu____3318 =
                                 let uu____3322 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3322) in
                               FStar_Syntax_Syntax.NT uu____3318 in
                             uu____3317 :: (env2.subst) in
                           {
                             env = (uu___115_3314.env);
                             subst = uu____3315;
                             tc_const = (uu___115_3314.tc_const)
                           } in
                         let uu____3323 =
                           let uu____3325 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3326 =
                             let uu____3328 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3328 :: acc in
                           uu____3325 :: uu____3326 in
                         (env3, uu____3323)
                       else
                         (let x =
                            let uu___116_3332 = bv in
                            let uu____3333 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___116_3332.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___116_3332.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3333
                            } in
                          let uu____3335 =
                            let uu____3337 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3337 :: acc in
                          (env2, uu____3335))) (env1, []) binders1 in
          (match uu____3253 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3349 =
                 let check_what =
                   let uu____3361 = is_monadic rc_opt1 in
                   if uu____3361 then check_m else check_n in
                 let uu____3370 = check_what env2 body1 in
                 match uu____3370 with
                 | (t,s_body,u_body) ->
                     let uu____3380 =
                       let uu____3381 =
                         let uu____3382 = is_monadic rc_opt1 in
                         if uu____3382 then M t else N t in
                       comp_of_nm uu____3381 in
                     (uu____3380, s_body, u_body) in
               (match uu____3349 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____3399 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___97_3402  ->
                                           match uu___97_3402 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____3403 -> false)) in
                                 if uu____3399
                                 then
                                   let uu____3404 =
                                     FStar_List.filter
                                       (fun uu___98_3407  ->
                                          match uu___98_3407 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____3408 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____3404
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____3414 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___99_3417  ->
                                         match uu___99_3417 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____3418 -> false)) in
                               if uu____3414
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___100_3423  ->
                                        match uu___100_3423 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____3424 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu____3425 =
                                   let uu____3426 =
                                     let uu____3429 = double_star rt in
                                     FStar_Pervasives_Native.Some uu____3429 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____3426 flags in
                                 FStar_Pervasives_Native.Some uu____3425
                               else
                                 (let uu____3431 =
                                    let uu___117_3432 = rc in
                                    let uu____3433 =
                                      let uu____3436 = star_type' env2 rt in
                                      FStar_Pervasives_Native.Some uu____3436 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___117_3432.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____3433;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___117_3432.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu____3431)) in
                    let uu____3437 =
                      let comp1 =
                        let uu____3443 = is_monadic rc_opt1 in
                        let uu____3444 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3443 uu____3444 in
                      let uu____3445 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu____3445,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu____3437 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu____3469 =
                             let uu____3470 =
                               let uu____3479 =
                                 let uu____3481 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu____3481 s_rc_opt in
                               (s_binders1, s_body1, uu____3479) in
                             FStar_Syntax_Syntax.Tm_abs uu____3470 in
                           mk1 uu____3469 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu____3488 =
                             let uu____3489 =
                               let uu____3498 =
                                 let uu____3500 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu____3500 u_rc_opt in
                               (u_binders2, u_body2, uu____3498) in
                             FStar_Syntax_Syntax.Tm_abs uu____3489 in
                           mk1 uu____3488 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____3506;_};
            FStar_Syntax_Syntax.fv_delta = uu____3507;
            FStar_Syntax_Syntax.fv_qual = uu____3508;_}
          ->
          let uu____3510 =
            let uu____3513 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____3513 in
          (match uu____3510 with
           | (uu____3529,t) ->
               let uu____3531 = let uu____3532 = normalize1 t in N uu____3532 in
               (uu____3531, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3545 = check_n env head1 in
          (match uu____3545 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3559 =
                   let uu____3560 = FStar_Syntax_Subst.compress t in
                   uu____3560.FStar_Syntax_Syntax.n in
                 match uu____3559 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3562 -> true
                 | uu____3569 -> false in
               let rec flatten1 t =
                 let uu____3580 =
                   let uu____3581 = FStar_Syntax_Subst.compress t in
                   uu____3581.FStar_Syntax_Syntax.n in
                 match uu____3580 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____3591);
                                FStar_Syntax_Syntax.pos = uu____3592;
                                FStar_Syntax_Syntax.vars = uu____3593;_})
                     when is_arrow t1 ->
                     let uu____3606 = flatten1 t1 in
                     (match uu____3606 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3650,uu____3651)
                     -> flatten1 e1
                 | uu____3672 ->
                     let uu____3673 =
                       let uu____3674 =
                         let uu____3675 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____3675 in
                       FStar_Errors.Err uu____3674 in
                     raise uu____3673 in
               let uu____3682 = flatten1 t_head in
               (match uu____3682 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____3729 =
                          let uu____3730 =
                            let uu____3731 = FStar_Util.string_of_int n1 in
                            let uu____3738 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____3749 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____3731 uu____3738 uu____3749 in
                          FStar_Errors.Err uu____3730 in
                        raise uu____3729)
                     else ();
                     (let uu____3757 =
                        FStar_Syntax_Subst.open_comp binders comp in
                      match uu____3757 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____3783 args1 =
                            match uu____3783 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____3822 =
                                       let uu____3823 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2 in
                                       uu____3823.FStar_Syntax_Syntax.n in
                                     nm_of_comp uu____3822
                                 | (binders3,[]) ->
                                     let uu____3839 =
                                       let uu____3840 =
                                         let uu____3842 =
                                           let uu____3843 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____3843 in
                                         FStar_Syntax_Subst.compress
                                           uu____3842 in
                                       uu____3840.FStar_Syntax_Syntax.n in
                                     (match uu____3839 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____3857 =
                                            let uu____3858 =
                                              let uu____3859 =
                                                let uu____3866 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu____3866) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____3859 in
                                            mk1 uu____3858 in
                                          N uu____3857
                                      | uu____3870 -> failwith "wat?")
                                 | ([],uu____3871::uu____3872) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____3893)::binders3,(arg,uu____3896)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu____3924 = FStar_List.splitAt n' binders1 in
                          (match uu____3924 with
                           | (binders2,uu____3943) ->
                               let uu____3956 =
                                 let uu____3966 =
                                   FStar_List.map2
                                     (fun uu____3995  ->
                                        fun uu____3996  ->
                                          match (uu____3995, uu____3996) with
                                          | ((bv,uu____4013),(arg,q)) ->
                                              let uu____4020 =
                                                let uu____4021 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4021.FStar_Syntax_Syntax.n in
                                              (match uu____4020 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4030 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4043 ->
                                                   let uu____4044 =
                                                     check_n env arg in
                                                   (match uu____4044 with
                                                    | (uu____4055,s_arg,u_arg)
                                                        ->
                                                        let uu____4058 =
                                                          let uu____4062 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4062
                                                          then
                                                            let uu____4066 =
                                                              let uu____4069
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4069, q) in
                                                            [uu____4066;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4058))))
                                     binders2 args in
                                 FStar_List.split uu____3966 in
                               (match uu____3956 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4116 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4121 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4116, uu____4121)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4157) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4161) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4165,uu____4166) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4188 = let uu____4189 = env.tc_const c in N uu____4189 in
          (uu____4188, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4190 ->
          let uu____4197 =
            let uu____4198 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4198 in
          failwith uu____4197
      | FStar_Syntax_Syntax.Tm_type uu____4202 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4206 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4216 ->
          let uu____4220 =
            let uu____4221 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4221 in
          failwith uu____4220
      | FStar_Syntax_Syntax.Tm_uvar uu____4225 ->
          let uu____4234 =
            let uu____4235 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4235 in
          failwith uu____4234
      | FStar_Syntax_Syntax.Tm_delayed uu____4239 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4255 =
            let uu____4256 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4256 in
          failwith uu____4255
and mk_match:
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
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
          let uu____4288 = check_n env e0 in
          match uu____4288 with
          | (uu____4295,s_e0,u_e0) ->
              let uu____4298 =
                let uu____4313 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4349 = FStar_Syntax_Subst.open_branch b in
                       match uu____4349 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___118_4372 = env in
                             let uu____4373 =
                               let uu____4374 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4374 in
                             {
                               env = uu____4373;
                               subst = (uu___118_4372.subst);
                               tc_const = (uu___118_4372.tc_const)
                             } in
                           let uu____4376 = f env1 body in
                           (match uu____4376 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____4414 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____4313 in
              (match uu____4298 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____4467 = FStar_List.hd nms in
                     match uu____4467 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___101_4473  ->
                          match uu___101_4473 with
                          | M uu____4474 -> true
                          | uu____4475 -> false) nms in
                   let uu____4476 =
                     let uu____4495 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____4545  ->
                              match uu____4545 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____4638 =
                                         check env original_body (M t2) in
                                       (match uu____4638 with
                                        | (uu____4657,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____4678,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____4495 in
                   (match uu____4476 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____4776  ->
                                 match uu____4776 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____4804 =
                                         let uu____4805 =
                                           let uu____4813 =
                                             let uu____4817 =
                                               let uu____4820 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____4821 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____4820, uu____4821) in
                                             [uu____4817] in
                                           (s_body, uu____4813) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____4805 in
                                       mk1 uu____4804 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____4839 =
                              let uu____4840 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____4840] in
                            let uu____4841 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            FStar_Syntax_Util.abs uu____4839 uu____4841
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu____4845 =
                              let uu____4849 =
                                let uu____4850 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____4850 in
                              [uu____4849] in
                            let uu____4851 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____4845 uu____4851 in
                          let uu____4853 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu____4873 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____4853, uu____4873)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____4884 =
                             let uu____4886 =
                               let uu____4887 =
                                 let uu____4901 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____4901,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____4887 in
                             mk1 uu____4886 in
                           let uu____4920 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____4884, uu____4920))))
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
              let uu____4957 = FStar_Syntax_Syntax.mk_binder x in
              [uu____4957] in
            let uu____4958 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____4958 with
            | (x_binders1,e21) ->
                let uu____4966 = infer env e1 in
                (match uu____4966 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____4977 = is_C t1 in
                       if uu____4977
                       then
                         let uu___119_4978 = binding in
                         let uu____4979 =
                           let uu____4981 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____4981 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___119_4978.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___119_4978.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____4979;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___119_4978.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___119_4978.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___120_4984 = env in
                       let uu____4985 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_4987 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_4987.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_4987.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____4985;
                         subst = (uu___120_4984.subst);
                         tc_const = (uu___120_4984.tc_const)
                       } in
                     let uu____4988 = proceed env1 e21 in
                     (match uu____4988 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___122_4999 = binding in
                            let uu____5000 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___122_4999.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___122_4999.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5000;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___122_4999.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___122_4999.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5002 =
                            let uu____5004 =
                              let uu____5005 =
                                let uu____5012 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___123_5018 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___123_5018.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___123_5018.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___123_5018.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___123_5018.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5012) in
                              FStar_Syntax_Syntax.Tm_let uu____5005 in
                            mk1 uu____5004 in
                          let uu____5019 =
                            let uu____5021 =
                              let uu____5022 =
                                let uu____5029 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___124_5035 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___124_5035.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___124_5035.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___124_5035.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___124_5035.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5029) in
                              FStar_Syntax_Syntax.Tm_let uu____5022 in
                            mk1 uu____5021 in
                          (nm_rec, uu____5002, uu____5019))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___125_5042 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___125_5042.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___125_5042.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___125_5042.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___126_5044 = env in
                       let uu____5045 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___127_5047 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_5047.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_5047.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5045;
                         subst = (uu___126_5044.subst);
                         tc_const = (uu___126_5044.tc_const)
                       } in
                     let uu____5048 = ensure_m env1 e21 in
                     (match uu____5048 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu____5063 =
                              let uu____5064 =
                                let uu____5072 =
                                  let uu____5076 =
                                    let uu____5079 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____5080 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5079, uu____5080) in
                                  [uu____5076] in
                                (s_e2, uu____5072) in
                              FStar_Syntax_Syntax.Tm_app uu____5064 in
                            mk1 uu____5063 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu____5091 =
                              let uu____5092 =
                                let uu____5100 =
                                  let uu____5104 =
                                    let uu____5107 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____5107) in
                                  [uu____5104] in
                                (s_e1, uu____5100) in
                              FStar_Syntax_Syntax.Tm_app uu____5092 in
                            mk1 uu____5091 in
                          let uu____5115 =
                            let uu____5116 =
                              let uu____5117 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5117] in
                            FStar_Syntax_Util.abs uu____5116 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu____5118 =
                            let uu____5120 =
                              let uu____5121 =
                                let uu____5128 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___128_5134 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___128_5134.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___128_5134.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___128_5134.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___128_5134.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5128) in
                              FStar_Syntax_Syntax.Tm_let uu____5121 in
                            mk1 uu____5120 in
                          ((M t2), uu____5115, uu____5118)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5142 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        N uu____5142 in
      let uu____5146 = check env e mn in
      match uu____5146 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5156 -> failwith "[check_n]: impossible"
and check_m:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5169 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos in
        M uu____5169 in
      let uu____5173 = check env e mn in
      match uu____5173 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5183 -> failwith "[check_m]: impossible"
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
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun t  -> FStar_Syntax_Util.comp_result t
and trans_F_:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____5203 =
           let uu____5204 = is_C c in Prims.op_Negation uu____5204 in
         if uu____5203 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos in
         let uu____5214 =
           let uu____5215 = FStar_Syntax_Subst.compress c in
           uu____5215.FStar_Syntax_Syntax.n in
         match uu____5214 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5229 = FStar_Syntax_Util.head_and_args wp in
             (match uu____5229 with
              | (wp_head,wp_args) ->
                  ((let uu____5250 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5266 =
                           let uu____5267 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5267 in
                         Prims.op_Negation uu____5266) in
                    if uu____5250 then failwith "mismatch" else ());
                   (let uu____5278 =
                      let uu____5279 =
                        let uu____5287 =
                          FStar_List.map2
                            (fun uu____5306  ->
                               fun uu____5307  ->
                                 match (uu____5306, uu____5307) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____5330 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____5330
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____5333 = print_implicit q in
                                         let uu____5334 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____5333 uu____5334)
                                      else ();
                                      (let uu____5336 =
                                         trans_F_ env arg wp_arg in
                                       (uu____5336, q)))) args wp_args in
                        (head1, uu____5287) in
                      FStar_Syntax_Syntax.Tm_app uu____5279 in
                    mk1 uu____5278)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____5355 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____5355 with
              | (binders_orig,comp1) ->
                  let uu____5360 =
                    let uu____5368 =
                      FStar_List.map
                        (fun uu____5389  ->
                           match uu____5389 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____5401 = is_C h in
                               if uu____5401
                               then
                                 let w' =
                                   let uu____5408 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____5408 in
                                 let uu____5409 =
                                   let uu____5413 =
                                     let uu____5417 =
                                       let uu____5420 =
                                         let uu____5421 =
                                           let uu____5422 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____5422 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____5421 in
                                       (uu____5420, q) in
                                     [uu____5417] in
                                   (w', q) :: uu____5413 in
                                 (w', uu____5409)
                               else
                                 (let x =
                                    let uu____5434 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____5434 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____5368 in
                  (match uu____5360 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____5464 =
                           let uu____5466 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____5466 in
                         FStar_Syntax_Subst.subst_comp uu____5464 comp1 in
                       let app =
                         let uu____5469 =
                           let uu____5470 =
                             let uu____5478 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____5488 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____5489 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____5488, uu____5489)) bvs in
                             (wp, uu____5478) in
                           FStar_Syntax_Syntax.Tm_app uu____5470 in
                         mk1 uu____5469 in
                       let comp3 =
                         let uu____5494 = type_of_comp comp2 in
                         let uu____5495 = is_monadic_comp comp2 in
                         trans_G env uu____5494 uu____5495 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____5497,uu____5498) ->
             trans_F_ env e wp
         | uu____5519 -> failwith "impossible trans_F_")
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
            let uu____5524 =
              let uu____5525 = star_type' env h in
              let uu____5527 =
                let uu____5532 =
                  let uu____5535 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____5535) in
                [uu____5532] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____5525;
                FStar_Syntax_Syntax.effect_args = uu____5527;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____5524
          else
            (let uu____5541 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____5541)
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
    fun t  -> let uu____5556 = n env.env t in star_type' env uu____5556
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____5569 = n env.env t in check_n env uu____5569
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____5582 = n env.env c in
        let uu____5583 = n env.env wp in trans_F_ env uu____5582 uu____5583