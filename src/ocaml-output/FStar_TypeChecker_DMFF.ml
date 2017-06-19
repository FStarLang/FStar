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
              let uu___101_79 = a in
              let uu____80 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___101_79.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___101_79.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____80
              } in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s in
            (let uu____88 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
             if uu____88
             then
               (d "Elaborating extra WP combinators";
                (let uu____90 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu____90))
             else ());
            (let rec collect_binders t =
               let uu____99 =
                 let uu____100 =
                   let uu____103 = FStar_Syntax_Subst.compress t in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____103 in
                 uu____100.FStar_Syntax_Syntax.n in
               match uu____99 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____125) -> t1
                     | uu____132 -> failwith "wp_a contains non-Tot arrow" in
                   let uu____135 = collect_binders rest in
                   FStar_List.append bs uu____135
               | FStar_Syntax_Syntax.Tm_type uu____141 -> []
               | uu____144 -> failwith "wp_a doesn't end in Type0" in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu____156 = collect_binders wp_a1 in
               FStar_All.pipe_right uu____156 FStar_Syntax_Util.name_binders in
             (let uu____167 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED") in
              if uu____167
              then
                let uu____168 =
                  let uu____169 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu____169 in
                d uu____168
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk1 x =
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange in
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
                  (fun uu____230  ->
                     match uu____230 with
                     | (t,b) ->
                         let uu____237 = FStar_Syntax_Syntax.as_implicit b in
                         (t, uu____237)) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____254 = FStar_Syntax_Syntax.as_implicit true in
                     ((fst t), uu____254)) in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____267 = FStar_Syntax_Syntax.bv_to_name (fst bv) in
                     FStar_Syntax_Syntax.as_arg uu____267) in
              let uu____268 =
                let uu____280 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let body =
                      let uu____300 = f (FStar_Syntax_Syntax.bv_to_name t) in
                      FStar_Syntax_Util.arrow gamma uu____300 in
                    let uu____303 =
                      let uu____304 =
                        let uu____308 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu____309 =
                          let uu____311 = FStar_Syntax_Syntax.mk_binder t in
                          [uu____311] in
                        uu____308 :: uu____309 in
                      FStar_List.append binders uu____304 in
                    FStar_Syntax_Util.abs uu____303 body None in
                  let uu____319 = mk2 FStar_Syntax_Syntax.mk_Total in
                  let uu____320 = mk2 FStar_Syntax_Syntax.mk_GTotal in
                  (uu____319, uu____320) in
                match uu____280 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env gctx_lid gctx_def in
                    let mk_app1 fv t =
                      let uu____351 =
                        let uu____352 =
                          let uu____362 =
                            let uu____366 =
                              FStar_List.map
                                (fun uu____374  ->
                                   match uu____374 with
                                   | (bv,uu____380) ->
                                       let uu____381 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu____382 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu____381, uu____382)) binders in
                            let uu____383 =
                              let uu____387 =
                                let uu____390 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu____391 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu____390, uu____391) in
                              let uu____392 =
                                let uu____396 =
                                  let uu____399 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu____399) in
                                [uu____396] in
                              uu____387 :: uu____392 in
                            FStar_List.append uu____366 uu____383 in
                          (fv, uu____362) in
                        FStar_Syntax_Syntax.Tm_app uu____352 in
                      mk1 uu____351 in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv)) in
              match uu____268 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype in
                    let x =
                      let uu____445 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____445 in
                    let ret1 =
                      let uu____453 =
                        let uu____459 =
                          let uu____460 =
                            let uu____463 =
                              let uu____464 =
                                FStar_Syntax_Syntax.bv_to_name t in
                              mk_ctx uu____464 in
                            FStar_Syntax_Syntax.mk_Total uu____463 in
                          FStar_Syntax_Util.lcomp_of_comp uu____460 in
                        FStar_Util.Inl uu____459 in
                      Some uu____453 in
                    let body =
                      let uu____474 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu____474 ret1 in
                    let uu____475 =
                      let uu____476 = mk_all_implicit binders in
                      let uu____480 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu____476 uu____480 in
                    FStar_Syntax_Util.abs uu____475 body ret1 in
                  let c_pure1 =
                    let uu____495 = mk_lid "pure" in
                    register env1 uu____495 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let l =
                      let uu____500 =
                        let uu____501 =
                          let uu____502 =
                            let uu____506 =
                              let uu____507 =
                                let uu____508 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv None uu____508 in
                              FStar_Syntax_Syntax.mk_binder uu____507 in
                            [uu____506] in
                          let uu____509 =
                            let uu____512 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu____512 in
                          FStar_Syntax_Util.arrow uu____502 uu____509 in
                        mk_gctx uu____501 in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____500 in
                    let r =
                      let uu____514 =
                        let uu____515 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____515 in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____514 in
                    let ret1 =
                      let uu____523 =
                        let uu____529 =
                          let uu____530 =
                            let uu____533 =
                              let uu____534 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____534 in
                            FStar_Syntax_Syntax.mk_Total uu____533 in
                          FStar_Syntax_Util.lcomp_of_comp uu____530 in
                        FStar_Util.Inl uu____529 in
                      Some uu____523 in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma in
                      let inner_body =
                        let uu____549 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu____552 =
                          let uu____558 =
                            let uu____560 =
                              let uu____561 =
                                let uu____562 =
                                  FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu____562
                                  gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu____561 in
                            [uu____560] in
                          FStar_List.append gamma_as_args uu____558 in
                        FStar_Syntax_Util.mk_app uu____549 uu____552 in
                      FStar_Syntax_Util.abs gamma inner_body ret1 in
                    let uu____565 =
                      let uu____566 = mk_all_implicit binders in
                      let uu____570 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu____566 uu____570 in
                    FStar_Syntax_Util.abs uu____565 outer_body ret1 in
                  let c_app1 =
                    let uu____589 = mk_lid "app" in
                    register env1 uu____589 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____596 =
                        let uu____600 =
                          let uu____601 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____601 in
                        [uu____600] in
                      let uu____602 =
                        let uu____605 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu____605 in
                      FStar_Syntax_Util.arrow uu____596 uu____602 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____608 =
                        let uu____609 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____609 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____608 in
                    let ret1 =
                      let uu____617 =
                        let uu____623 =
                          let uu____624 =
                            let uu____627 =
                              let uu____628 =
                                FStar_Syntax_Syntax.bv_to_name t2 in
                              mk_gctx uu____628 in
                            FStar_Syntax_Syntax.mk_Total uu____627 in
                          FStar_Syntax_Util.lcomp_of_comp uu____624 in
                        FStar_Util.Inl uu____623 in
                      Some uu____617 in
                    let uu____637 =
                      let uu____638 = mk_all_implicit binders in
                      let uu____642 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu____638 uu____642 in
                    let uu____660 =
                      let uu____661 =
                        let uu____667 =
                          let uu____669 =
                            let uu____672 =
                              let uu____678 =
                                let uu____680 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu____680] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____678 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____672 in
                          let uu____681 =
                            let uu____685 =
                              FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu____685] in
                          uu____669 :: uu____681 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____667 in
                      FStar_Syntax_Util.mk_app c_app1 uu____661 in
                    FStar_Syntax_Util.abs uu____637 uu____660 ret1 in
                  let c_lift11 =
                    let uu____689 = mk_lid "lift1" in
                    register env1 uu____689 c_lift1 in
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
                      let uu____697 =
                        let uu____701 =
                          let uu____702 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu____702 in
                        let uu____703 =
                          let uu____705 =
                            let uu____706 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu____706 in
                          [uu____705] in
                        uu____701 :: uu____703 in
                      let uu____707 =
                        let uu____710 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu____710 in
                      FStar_Syntax_Util.arrow uu____697 uu____707 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let a11 =
                      let uu____713 =
                        let uu____714 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu____714 in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____713 in
                    let a2 =
                      let uu____716 =
                        let uu____717 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu____717 in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____716 in
                    let ret1 =
                      let uu____725 =
                        let uu____731 =
                          let uu____732 =
                            let uu____735 =
                              let uu____736 =
                                FStar_Syntax_Syntax.bv_to_name t3 in
                              mk_gctx uu____736 in
                            FStar_Syntax_Syntax.mk_Total uu____735 in
                          FStar_Syntax_Util.lcomp_of_comp uu____732 in
                        FStar_Util.Inl uu____731 in
                      Some uu____725 in
                    let uu____745 =
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
                    FStar_Syntax_Util.abs uu____745 uu____772 ret1 in
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
                        let uu____879 =
                          let uu____883 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu____883] in
                        FStar_List.append gamma uu____879 in
                      let uu____886 =
                        let uu____887 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu____890 =
                          let uu____896 =
                            let uu____897 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu____897 in
                          let uu____898 = args_of_binders1 gamma in uu____896
                            :: uu____898 in
                        FStar_Syntax_Util.mk_app uu____887 uu____890 in
                      FStar_Syntax_Util.abs uu____878 uu____886 ret1 in
                    let uu____900 =
                      let uu____901 = mk_all_implicit binders in
                      let uu____905 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu____901 uu____905 in
                    FStar_Syntax_Util.abs uu____900 body ret1 in
                  let c_push1 =
                    let uu____922 = mk_lid "push" in
                    register env1 uu____922 c_push in
                  let ret_tot_wp_a =
                    let uu____930 =
                      let uu____936 =
                        let uu____937 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.lcomp_of_comp uu____937 in
                      FStar_Util.Inl uu____936 in
                    Some uu____930 in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____968 =
                        let uu____969 =
                          let uu____979 = args_of_binders1 binders in
                          (c, uu____979) in
                        FStar_Syntax_Syntax.Tm_app uu____969 in
                      mk1 uu____968
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____987 =
                        let uu____988 =
                          let uu____992 =
                            FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu____993 =
                            let uu____995 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu____995] in
                          uu____992 :: uu____993 in
                        let uu____996 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu____988 uu____996 in
                      FStar_Syntax_Syntax.mk_Total uu____987 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype in
                    let uu____1000 =
                      let uu____1001 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu____1001 in
                    let uu____1007 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None in
                      let uu____1009 =
                        let uu____1012 =
                          let uu____1018 =
                            let uu____1020 =
                              let uu____1023 =
                                let uu____1029 =
                                  let uu____1030 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu____1030 in
                                [uu____1029] in
                              FStar_Syntax_Util.mk_app l_ite uu____1023 in
                            [uu____1020] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1018 in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1012 in
                      FStar_Syntax_Util.ascribe uu____1009
                        ((FStar_Util.Inr result_comp), None) in
                    FStar_Syntax_Util.abs uu____1000 uu____1007
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp))) in
                  let wp_if_then_else1 =
                    let uu____1055 = mk_lid "wp_if_then_else" in
                    register env1 uu____1055 wp_if_then_else in
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
                      let uu____1066 =
                        let uu____1072 =
                          let uu____1074 =
                            let uu____1077 =
                              let uu____1083 =
                                let uu____1085 =
                                  let uu____1088 =
                                    let uu____1094 =
                                      let uu____1095 =
                                        FStar_Syntax_Syntax.bv_to_name q in
                                      FStar_Syntax_Syntax.as_arg uu____1095 in
                                    [uu____1094] in
                                  FStar_Syntax_Util.mk_app l_and uu____1088 in
                                [uu____1085] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1083 in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1077 in
                          let uu____1100 =
                            let uu____1104 =
                              FStar_Syntax_Syntax.bv_to_name wp in
                            [uu____1104] in
                          uu____1074 :: uu____1100 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1072 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1066 in
                    let uu____1107 =
                      let uu____1108 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1108 in
                    FStar_Syntax_Util.abs uu____1107 body ret_tot_wp_a in
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
                      let uu____1168 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp] in
                      FStar_List.append binders uu____1168 in
                    FStar_Syntax_Util.abs uu____1167 body ret_tot_wp_a in
                  let wp_assume1 =
                    let uu____1175 = mk_lid "wp_assume" in
                    register env1 uu____1175 wp_assume in
                  let wp_assume2 = mk_generic_app wp_assume1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu____1184 =
                        let uu____1188 =
                          let uu____1189 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu____1189 in
                        [uu____1188] in
                      let uu____1190 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu____1184 uu____1190 in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f in
                    let body =
                      let uu____1197 =
                        let uu____1203 =
                          let uu____1205 =
                            let uu____1208 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1208 in
                          let uu____1214 =
                            let uu____1218 =
                              let uu____1221 =
                                let uu____1227 =
                                  let uu____1229 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu____1229] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1227 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1221 in
                            [uu____1218] in
                          uu____1205 :: uu____1214 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1203 in
                      FStar_Syntax_Util.mk_app c_app1 uu____1197 in
                    let uu____1236 =
                      let uu____1237 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu____1237 in
                    FStar_Syntax_Util.abs uu____1236 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu____1244 = mk_lid "wp_close" in
                    register env1 uu____1244 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    let uu____1255 =
                      let uu____1261 =
                        let uu____1262 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1262 in
                      FStar_Util.Inl uu____1261 in
                    Some uu____1255 in
                  let ret_gtot_type =
                    let uu____1282 =
                      let uu____1288 =
                        let uu____1289 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1289 in
                      FStar_Util.Inl uu____1288 in
                    Some uu____1282 in
                  let mk_forall1 x body =
                    let uu____1309 =
                      let uu____1312 =
                        let uu____1313 =
                          let uu____1323 =
                            let uu____1325 =
                              let uu____1326 =
                                let uu____1327 =
                                  let uu____1328 =
                                    FStar_Syntax_Syntax.mk_binder x in
                                  [uu____1328] in
                                FStar_Syntax_Util.abs uu____1327 body
                                  ret_tot_type in
                              FStar_Syntax_Syntax.as_arg uu____1326 in
                            [uu____1325] in
                          (FStar_Syntax_Util.tforall, uu____1323) in
                        FStar_Syntax_Syntax.Tm_app uu____1313 in
                      FStar_Syntax_Syntax.mk uu____1312 in
                    uu____1309 None FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu____1342 =
                      let uu____1343 = FStar_Syntax_Subst.compress t in
                      uu____1343.FStar_Syntax_Syntax.n in
                    match uu____1342 with
                    | FStar_Syntax_Syntax.Tm_type uu____1346 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1361  ->
                              match uu____1361 with
                              | (b,uu____1365) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1366 -> true in
                  let rec is_monotonic t =
                    let uu____1371 =
                      let uu____1372 = FStar_Syntax_Subst.compress t in
                      uu____1372.FStar_Syntax_Syntax.n in
                    match uu____1371 with
                    | FStar_Syntax_Syntax.Tm_type uu____1375 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1390  ->
                              match uu____1390 with
                              | (b,uu____1394) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1395 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t in
                    let uu____1447 =
                      let uu____1448 = FStar_Syntax_Subst.compress t1 in
                      uu____1448.FStar_Syntax_Syntax.n in
                    match uu____1447 with
                    | FStar_Syntax_Syntax.Tm_type uu____1451 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1454);
                                      FStar_Syntax_Syntax.tk = uu____1455;
                                      FStar_Syntax_Syntax.pos = uu____1456;
                                      FStar_Syntax_Syntax.vars = uu____1457;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1480 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1480
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1483 =
                              let uu____1486 =
                                let uu____1492 =
                                  let uu____1493 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1493 in
                                [uu____1492] in
                              FStar_Syntax_Util.mk_app x uu____1486 in
                            let uu____1494 =
                              let uu____1497 =
                                let uu____1503 =
                                  let uu____1504 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1504 in
                                [uu____1503] in
                              FStar_Syntax_Util.mk_app y uu____1497 in
                            mk_rel1 b uu____1483 uu____1494 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1509 =
                               let uu____1510 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1513 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1510 uu____1513 in
                             let uu____1516 =
                               let uu____1517 =
                                 let uu____1520 =
                                   let uu____1526 =
                                     let uu____1527 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1527 in
                                   [uu____1526] in
                                 FStar_Syntax_Util.mk_app x uu____1520 in
                               let uu____1528 =
                                 let uu____1531 =
                                   let uu____1537 =
                                     let uu____1538 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1538 in
                                   [uu____1537] in
                                 FStar_Syntax_Util.mk_app y uu____1531 in
                               mk_rel1 b uu____1517 uu____1528 in
                             FStar_Syntax_Util.mk_imp uu____1509 uu____1516 in
                           let uu____1539 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1539)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1542);
                                      FStar_Syntax_Syntax.tk = uu____1543;
                                      FStar_Syntax_Syntax.pos = uu____1544;
                                      FStar_Syntax_Syntax.vars = uu____1545;_})
                        ->
                        let a2 = (fst binder).FStar_Syntax_Syntax.sort in
                        let uu____1568 =
                          (is_monotonic a2) || (is_monotonic b) in
                        if uu____1568
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                          let body =
                            let uu____1571 =
                              let uu____1574 =
                                let uu____1580 =
                                  let uu____1581 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1581 in
                                [uu____1580] in
                              FStar_Syntax_Util.mk_app x uu____1574 in
                            let uu____1582 =
                              let uu____1585 =
                                let uu____1591 =
                                  let uu____1592 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu____1592 in
                                [uu____1591] in
                              FStar_Syntax_Util.mk_app y uu____1585 in
                            mk_rel1 b uu____1571 uu____1582 in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2 in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2 in
                           let body =
                             let uu____1597 =
                               let uu____1598 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu____1601 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu____1598 uu____1601 in
                             let uu____1604 =
                               let uu____1605 =
                                 let uu____1608 =
                                   let uu____1614 =
                                     let uu____1615 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu____1615 in
                                   [uu____1614] in
                                 FStar_Syntax_Util.mk_app x uu____1608 in
                               let uu____1616 =
                                 let uu____1619 =
                                   let uu____1625 =
                                     let uu____1626 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu____1626 in
                                   [uu____1625] in
                                 FStar_Syntax_Util.mk_app y uu____1619 in
                               mk_rel1 b uu____1605 uu____1616 in
                             FStar_Syntax_Util.mk_imp uu____1597 uu____1604 in
                           let uu____1627 = mk_forall1 a21 body in
                           mk_forall1 a11 uu____1627)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___102_1648 = t1 in
                          let uu____1649 =
                            let uu____1650 =
                              let uu____1658 =
                                let uu____1659 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu____1659 in
                              ([binder], uu____1658) in
                            FStar_Syntax_Syntax.Tm_arrow uu____1650 in
                          {
                            FStar_Syntax_Syntax.n = uu____1649;
                            FStar_Syntax_Syntax.tk =
                              (uu___102_1648.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___102_1648.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___102_1648.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1671 ->
                        failwith "unhandled arrow"
                    | uu____1679 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
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
                      let uu____1694 =
                        let uu____1695 = FStar_Syntax_Subst.compress t1 in
                        uu____1695.FStar_Syntax_Syntax.n in
                      match uu____1694 with
                      | FStar_Syntax_Syntax.Tm_type uu____1698 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1715 = FStar_Syntax_Subst.compress head1 in
                          FStar_Syntax_Util.is_tuple_constructor uu____1715
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1730 =
                                let uu____1731 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1731 i in
                              FStar_Syntax_Syntax.fvar uu____1730
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)] in
                          let uu____1755 =
                            let uu____1759 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1764  ->
                                     match uu____1764 with
                                     | (t2,q) ->
                                         let uu____1769 = project i x in
                                         let uu____1770 = project i y in
                                         mk_stronger t2 uu____1769 uu____1770)
                                args in
                            match uu____1759 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu____1755 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1787);
                                      FStar_Syntax_Syntax.tk = uu____1788;
                                      FStar_Syntax_Syntax.pos = uu____1789;
                                      FStar_Syntax_Syntax.vars = uu____1790;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1812  ->
                                   match uu____1812 with
                                   | (bv,q) ->
                                       let uu____1817 =
                                         let uu____1818 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1818 in
                                       FStar_Syntax_Syntax.gen_bv uu____1817
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1822 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1822) bvs in
                          let body =
                            let uu____1824 = FStar_Syntax_Util.mk_app x args in
                            let uu____1825 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1824 uu____1825 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1830);
                                      FStar_Syntax_Syntax.tk = uu____1831;
                                      FStar_Syntax_Syntax.pos = uu____1832;
                                      FStar_Syntax_Syntax.vars = uu____1833;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____1855  ->
                                   match uu____1855 with
                                   | (bv,q) ->
                                       let uu____1860 =
                                         let uu____1861 =
                                           FStar_Util.string_of_int i in
                                         Prims.strcat "a" uu____1861 in
                                       FStar_Syntax_Syntax.gen_bv uu____1860
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1865 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu____1865) bvs in
                          let body =
                            let uu____1867 = FStar_Syntax_Util.mk_app x args in
                            let uu____1868 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu____1867 uu____1868 in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1871 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu____1873 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu____1874 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu____1875 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu____1873 uu____1874 uu____1875 in
                    let uu____1876 =
                      let uu____1877 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu____1877 in
                    FStar_Syntax_Util.abs uu____1876 body ret_tot_type in
                  let stronger1 =
                    let uu____1892 = mk_lid "stronger" in
                    register env1 uu____1892 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____1898 = FStar_Util.prefix gamma in
                    match uu____1898 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (fst post).FStar_Syntax_Syntax.sort in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq1 =
                            let uu____1924 =
                              FStar_Syntax_Syntax.bv_to_name (fst post) in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1924 in
                          let uu____1927 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1 in
                          match uu____1927 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1935 = args_of_binders1 binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu____1935 in
                              let guard_free1 =
                                let uu____1942 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None in
                                FStar_Syntax_Syntax.fv_to_tm uu____1942 in
                              let pat =
                                let uu____1946 =
                                  let uu____1952 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu____1952] in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1946 in
                              let pattern_guarded_body =
                                let uu____1956 =
                                  let uu____1957 =
                                    let uu____1962 =
                                      let uu____1963 =
                                        let uu____1970 =
                                          let uu____1972 =
                                            FStar_Syntax_Syntax.as_arg pat in
                                          [uu____1972] in
                                        [uu____1970] in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1963 in
                                    (body, uu____1962) in
                                  FStar_Syntax_Syntax.Tm_meta uu____1957 in
                                mk1 uu____1956 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1975 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu____1978 =
                            let uu____1979 =
                              let uu____1980 =
                                let uu____1981 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu____1984 =
                                  let uu____1990 = args_of_binders1 wp_args in
                                  let uu____1992 =
                                    let uu____1994 =
                                      let uu____1995 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu____1995 in
                                    [uu____1994] in
                                  FStar_List.append uu____1990 uu____1992 in
                                FStar_Syntax_Util.mk_app uu____1981
                                  uu____1984 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____1980 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1979 in
                          FStar_Syntax_Util.abs gamma uu____1978
                            ret_gtot_type in
                        let uu____1996 =
                          let uu____1997 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu____1997 in
                        FStar_Syntax_Util.abs uu____1996 body ret_gtot_type in
                  let wp_ite1 =
                    let uu____2004 = mk_lid "wp_ite" in
                    register env1 uu____2004 wp_ite in
                  let wp_ite2 = mk_generic_app wp_ite1 in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let uu____2010 = FStar_Util.prefix gamma in
                    match uu____2010 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu____2034 =
                            let uu____2035 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name (fst post) in
                            let uu____2038 =
                              let uu____2044 =
                                let uu____2045 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu____2045 in
                              [uu____2044] in
                            FStar_Syntax_Util.mk_app uu____2035 uu____2038 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2034 in
                        let uu____2046 =
                          let uu____2047 =
                            let uu____2051 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu____2051 gamma in
                          FStar_List.append binders uu____2047 in
                        FStar_Syntax_Util.abs uu____2046 body ret_gtot_type in
                  let null_wp1 =
                    let uu____2060 = mk_lid "null_wp" in
                    register env1 uu____2060 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1 in
                    let body =
                      let uu____2069 =
                        let uu____2075 =
                          let uu____2077 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu____2078 =
                            let uu____2080 =
                              let uu____2083 =
                                let uu____2089 =
                                  let uu____2090 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu____2090 in
                                [uu____2089] in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2083 in
                            let uu____2091 =
                              let uu____2095 =
                                FStar_Syntax_Syntax.bv_to_name wp in
                              [uu____2095] in
                            uu____2080 :: uu____2091 in
                          uu____2077 :: uu____2078 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2075 in
                      FStar_Syntax_Util.mk_app stronger2 uu____2069 in
                    let uu____2098 =
                      let uu____2099 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu____2099 in
                    FStar_Syntax_Util.abs uu____2098 body ret_tot_type in
                  let wp_trivial1 =
                    let uu____2106 = mk_lid "wp_trivial" in
                    register env1 uu____2106 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu____2111 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED") in
                    if uu____2111
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let uu____2116 =
                      let uu____2118 = FStar_ST.read sigelts in
                      FStar_List.rev uu____2118 in
                    let uu____2123 =
                      let uu___103_2124 = ed in
                      let uu____2125 =
                        let uu____2126 = c wp_if_then_else2 in
                        ([], uu____2126) in
                      let uu____2128 =
                        let uu____2129 = c wp_ite2 in ([], uu____2129) in
                      let uu____2131 =
                        let uu____2132 = c stronger2 in ([], uu____2132) in
                      let uu____2134 =
                        let uu____2135 = c wp_close2 in ([], uu____2135) in
                      let uu____2137 =
                        let uu____2138 = c wp_assert2 in ([], uu____2138) in
                      let uu____2140 =
                        let uu____2141 = c wp_assume2 in ([], uu____2141) in
                      let uu____2143 =
                        let uu____2144 = c null_wp2 in ([], uu____2144) in
                      let uu____2146 =
                        let uu____2147 = c wp_trivial2 in ([], uu____2147) in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___103_2124.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___103_2124.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___103_2124.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___103_2124.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___103_2124.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___103_2124.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___103_2124.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2125;
                        FStar_Syntax_Syntax.ite_wp = uu____2128;
                        FStar_Syntax_Syntax.stronger = uu____2131;
                        FStar_Syntax_Syntax.close_wp = uu____2134;
                        FStar_Syntax_Syntax.assert_p = uu____2137;
                        FStar_Syntax_Syntax.assume_p = uu____2140;
                        FStar_Syntax_Syntax.null_wp = uu____2143;
                        FStar_Syntax_Syntax.trivial = uu____2146;
                        FStar_Syntax_Syntax.repr =
                          (uu___103_2124.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___103_2124.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___103_2124.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___103_2124.FStar_Syntax_Syntax.actions)
                      } in
                    (uu____2116, uu____2123)))))
type env_ = env
let get_env: env -> FStar_TypeChecker_Env.env = fun env  -> env.env
let set_env: env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___104_2162 = dmff_env in
      {
        env = env';
        subst = (uu___104_2162.subst);
        tc_const = (uu___104_2162.tc_const)
      }
type nm =
  | N of FStar_Syntax_Syntax.typ
  | M of FStar_Syntax_Syntax.typ
let uu___is_N: nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2176 -> false
let __proj__N__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0
let uu___is_M: nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2190 -> false
let __proj__M__item___0: nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0
type nm_ = nm
let nm_of_comp: FStar_Syntax_Syntax.comp' -> nm =
  fun uu___90_2202  ->
    match uu___90_2202 with
    | FStar_Syntax_Syntax.Total (t,uu____2204) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___89_2213  ->
                match uu___89_2213 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2214 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2216 =
          let uu____2217 =
            let uu____2218 = FStar_Syntax_Syntax.mk_Comp c in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2218 in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2217 in
        failwith uu____2216
    | FStar_Syntax_Syntax.GTotal uu____2219 ->
        failwith "[nm_of_comp]: impossible (GTot)"
let string_of_nm: nm -> Prims.string =
  fun uu___91_2228  ->
    match uu___91_2228 with
    | N t ->
        let uu____2230 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu____2230
    | M t ->
        let uu____2232 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu____2232
let is_monadic_arrow: FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2237,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2239;
                      FStar_Syntax_Syntax.pos = uu____2240;
                      FStar_Syntax_Syntax.vars = uu____2241;_})
        -> nm_of_comp n2
    | uu____2252 -> failwith "unexpected_argument: [is_monadic_arrow]"
let is_monadic_comp c =
  let uu____2266 = nm_of_comp c.FStar_Syntax_Syntax.n in
  match uu____2266 with | M uu____2267 -> true | N uu____2268 -> false
exception Not_found
let uu___is_Not_found: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2273 -> false
let double_star:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2284 =
        let uu____2288 =
          let uu____2289 = FStar_Syntax_Syntax.new_bv None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2289 in
        [uu____2288] in
      let uu____2290 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu____2284 uu____2290 in
    let uu____2293 = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu____2293
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
          (let uu____2328 =
             let uu____2336 =
               let uu____2340 =
                 let uu____2343 =
                   let uu____2344 = star_type' env a in
                   FStar_Syntax_Syntax.null_bv uu____2344 in
                 let uu____2345 = FStar_Syntax_Syntax.as_implicit false in
                 (uu____2343, uu____2345) in
               [uu____2340] in
             let uu____2350 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
             (uu____2336, uu____2350) in
           FStar_Syntax_Syntax.Tm_arrow uu____2328)
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2379) ->
          let binders1 =
            FStar_List.map
              (fun uu____2398  ->
                 match uu____2398 with
                 | (bv,aqual) ->
                     let uu____2405 =
                       let uu___105_2406 = bv in
                       let uu____2407 =
                         star_type' env bv.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___105_2406.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___105_2406.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2407
                       } in
                     (uu____2405, aqual)) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2410,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2412);
                             FStar_Syntax_Syntax.tk = uu____2413;
                             FStar_Syntax_Syntax.pos = uu____2414;
                             FStar_Syntax_Syntax.vars = uu____2415;_})
               ->
               let uu____2432 =
                 let uu____2433 =
                   let uu____2441 =
                     let uu____2442 = star_type' env hn in
                     FStar_Syntax_Syntax.mk_GTotal uu____2442 in
                   (binders1, uu____2441) in
                 FStar_Syntax_Syntax.Tm_arrow uu____2433 in
               mk1 uu____2432
           | uu____2446 ->
               let uu____2447 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu____2447 with
                | N hn ->
                    let uu____2449 =
                      let uu____2450 =
                        let uu____2458 =
                          let uu____2459 = star_type' env hn in
                          FStar_Syntax_Syntax.mk_Total uu____2459 in
                        (binders1, uu____2458) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2450 in
                    mk1 uu____2449
                | M a ->
                    let uu____2464 =
                      let uu____2465 =
                        let uu____2473 =
                          let uu____2477 =
                            let uu____2481 =
                              let uu____2484 =
                                let uu____2485 = mk_star_to_type1 env a in
                                FStar_Syntax_Syntax.null_bv uu____2485 in
                              let uu____2486 =
                                FStar_Syntax_Syntax.as_implicit false in
                              (uu____2484, uu____2486) in
                            [uu____2481] in
                          FStar_List.append binders1 uu____2477 in
                        let uu____2493 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu____2473, uu____2493) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2465 in
                    mk1 uu____2464))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2544 = f x in
                    FStar_Util.string_builder_append strb uu____2544);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2548 = f x1 in
                         FStar_Util.string_builder_append strb uu____2548))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu____2550 = FStar_Syntax_Print.term_to_string t2 in
            let uu____2551 = string_of_set FStar_Syntax_Print.bv_to_string s in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2550 uu____2551 in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2559 =
              let uu____2560 = FStar_Syntax_Subst.compress ty in
              uu____2560.FStar_Syntax_Syntax.n in
            match uu____2559 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2575 =
                  let uu____2576 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu____2576 in
                if uu____2575
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2590 = FStar_Syntax_Free.names ty1 in
                         FStar_Util.set_intersect uu____2590 s in
                       let uu____2592 =
                         let uu____2593 = FStar_Util.set_is_empty sinter in
                         Prims.op_Negation uu____2593 in
                       if uu____2592
                       then (debug1 ty1 sinter; raise Not_found)
                       else () in
                     let uu____2596 = FStar_Syntax_Subst.open_comp binders c in
                     match uu____2596 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2607  ->
                                  match uu____2607 with
                                  | (bv,uu____2613) ->
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
            | uu____2628 ->
                ((let uu____2630 = FStar_Syntax_Print.term_to_string ty in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2630);
                 false) in
          let rec is_valid_application head2 =
            let uu____2635 =
              let uu____2636 = FStar_Syntax_Subst.compress head2 in
              uu____2636.FStar_Syntax_Syntax.n in
            match uu____2635 with
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
                  (let uu____2640 = FStar_Syntax_Subst.compress head2 in
                   FStar_Syntax_Util.is_tuple_constructor uu____2640)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2655 -> true
                 | uu____2665 ->
                     ((let uu____2667 =
                         FStar_Syntax_Print.term_to_string head2 in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2667);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar uu____2668 -> true
            | FStar_Syntax_Syntax.Tm_name uu____2669 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2671) ->
                is_valid_application t2
            | uu____2676 -> false in
          let uu____2677 = is_valid_application head1 in
          if uu____2677
          then
            let uu____2678 =
              let uu____2679 =
                let uu____2689 =
                  FStar_List.map
                    (fun uu____2699  ->
                       match uu____2699 with
                       | (t2,qual) ->
                           let uu____2712 = star_type' env t2 in
                           (uu____2712, qual)) args in
                (head1, uu____2689) in
              FStar_Syntax_Syntax.Tm_app uu____2679 in
            mk1 uu____2678
          else
            (let uu____2719 =
               let uu____2720 =
                 let uu____2721 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2721 in
               FStar_Errors.Err uu____2720 in
             raise uu____2719)
      | FStar_Syntax_Syntax.Tm_bvar uu____2722 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____2723 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____2724 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____2725 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2751 = FStar_Syntax_Subst.open_term binders repr in
          (match uu____2751 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___108_2757 = env in
                 let uu____2758 =
                   FStar_TypeChecker_Env.push_binders env.env binders1 in
                 {
                   env = uu____2758;
                   subst = (uu___108_2757.subst);
                   tc_const = (uu___108_2757.tc_const)
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
               ((let uu___109_2775 = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___109_2775.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___109_2775.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2782 =
            let uu____2783 =
              let uu____2788 = star_type' env t2 in (uu____2788, m) in
            FStar_Syntax_Syntax.Tm_meta uu____2783 in
          mk1 uu____2782
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2826 =
            let uu____2827 =
              let uu____2845 = star_type' env e in
              let uu____2846 =
                let uu____2856 =
                  let uu____2861 = star_type' env t2 in
                  FStar_Util.Inl uu____2861 in
                (uu____2856, None) in
              (uu____2845, uu____2846, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu____2827 in
          mk1 uu____2826
      | FStar_Syntax_Syntax.Tm_ascribed uu____2883 ->
          let uu____2901 =
            let uu____2902 =
              let uu____2903 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2903 in
            FStar_Errors.Err uu____2902 in
          raise uu____2901
      | FStar_Syntax_Syntax.Tm_refine uu____2904 ->
          let uu____2909 =
            let uu____2910 =
              let uu____2911 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2911 in
            FStar_Errors.Err uu____2910 in
          raise uu____2909
      | FStar_Syntax_Syntax.Tm_uinst uu____2912 ->
          let uu____2917 =
            let uu____2918 =
              let uu____2919 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2919 in
            FStar_Errors.Err uu____2918 in
          raise uu____2917
      | FStar_Syntax_Syntax.Tm_constant uu____2920 ->
          let uu____2921 =
            let uu____2922 =
              let uu____2923 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2923 in
            FStar_Errors.Err uu____2922 in
          raise uu____2921
      | FStar_Syntax_Syntax.Tm_match uu____2924 ->
          let uu____2940 =
            let uu____2941 =
              let uu____2942 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2942 in
            FStar_Errors.Err uu____2941 in
          raise uu____2940
      | FStar_Syntax_Syntax.Tm_let uu____2943 ->
          let uu____2951 =
            let uu____2952 =
              let uu____2953 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2953 in
            FStar_Errors.Err uu____2952 in
          raise uu____2951
      | FStar_Syntax_Syntax.Tm_uvar uu____2954 ->
          let uu____2963 =
            let uu____2964 =
              let uu____2965 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2965 in
            FStar_Errors.Err uu____2964 in
          raise uu____2963
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2966 =
            let uu____2967 =
              let uu____2968 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2968 in
            FStar_Errors.Err uu____2967 in
          raise uu____2966
      | FStar_Syntax_Syntax.Tm_delayed uu____2969 -> failwith "impossible"
let is_monadic uu___93_3004 =
  match uu___93_3004 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
      { FStar_Syntax_Syntax.eff_name = uu____3016;
        FStar_Syntax_Syntax.res_typ = uu____3017;
        FStar_Syntax_Syntax.cflags = flags;
        FStar_Syntax_Syntax.comp = uu____3019;_})
      ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3036  ->
              match uu___92_3036 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3037 -> false))
  | Some (FStar_Util.Inr (uu____3038,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___92_3051  ->
              match uu___92_3051 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____3052 -> false))
let rec is_C: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____3057 =
      let uu____3058 = FStar_Syntax_Subst.compress t in
      uu____3058.FStar_Syntax_Syntax.n in
    match uu____3057 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____3078 =
            let uu____3079 = FStar_List.hd args in fst uu____3079 in
          is_C uu____3078 in
        if r
        then
          ((let uu____3091 =
              let uu____3092 =
                FStar_List.for_all
                  (fun uu____3095  ->
                     match uu____3095 with | (h,uu____3099) -> is_C h) args in
              Prims.op_Negation uu____3092 in
            if uu____3091 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____3103 =
              let uu____3104 =
                FStar_List.for_all
                  (fun uu____3107  ->
                     match uu____3107 with
                     | (h,uu____3111) ->
                         let uu____3112 = is_C h in
                         Prims.op_Negation uu____3112) args in
              Prims.op_Negation uu____3104 in
            if uu____3103 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3126 = nm_of_comp comp.FStar_Syntax_Syntax.n in
        (match uu____3126 with
         | M t1 ->
             ((let uu____3129 = is_C t1 in
               if uu____3129 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____3133) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3139) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____3145,uu____3146) -> is_C t1
    | uu____3175 -> false
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
          let uu____3205 =
            let uu____3206 =
              let uu____3216 = FStar_Syntax_Syntax.bv_to_name p in
              let uu____3217 =
                let uu____3221 =
                  let uu____3224 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu____3224) in
                [uu____3221] in
              (uu____3216, uu____3217) in
            FStar_Syntax_Syntax.Tm_app uu____3206 in
          mk1 uu____3205 in
        let uu____3232 =
          let uu____3233 = FStar_Syntax_Syntax.mk_binder p in [uu____3233] in
        let uu____3234 =
          let uu____3241 =
            let uu____3247 =
              let uu____3248 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
              FStar_Syntax_Util.lcomp_of_comp uu____3248 in
            FStar_Util.Inl uu____3247 in
          Some uu____3241 in
        FStar_Syntax_Util.abs uu____3232 body uu____3234
let is_unknown: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___94_3262  ->
    match uu___94_3262 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3263 -> false
let rec check:
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm* FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____3397 =
          match uu____3397 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3418 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3419 =
                       let uu____3420 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2 in
                       FStar_TypeChecker_Rel.is_trivial uu____3420 in
                     Prims.op_Negation uu____3419) in
                if uu____3418
                then
                  let uu____3421 =
                    let uu____3422 =
                      let uu____3423 = FStar_Syntax_Print.term_to_string e in
                      let uu____3424 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____3425 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3423 uu____3424 uu____3425 in
                    FStar_Errors.Err uu____3422 in
                  raise uu____3421
                else () in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3439 = mk_return env t1 s_e in
                     ((M t1), uu____3439, u_e)))
               | (M t1,N t2) ->
                   let uu____3442 =
                     let uu____3443 =
                       let uu____3444 = FStar_Syntax_Print.term_to_string e in
                       let uu____3445 = FStar_Syntax_Print.term_to_string t1 in
                       let uu____3446 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3444 uu____3445 uu____3446 in
                     FStar_Errors.Err uu____3443 in
                   raise uu____3442) in
        let ensure_m env1 e2 =
          let strip_m uu___95_3472 =
            match uu___95_3472 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3482 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu____3493 =
                let uu____3494 =
                  let uu____3497 =
                    let uu____3498 = FStar_Syntax_Print.term_to_string t in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3498 in
                  (uu____3497, (e2.FStar_Syntax_Syntax.pos)) in
                FStar_Errors.Error uu____3494 in
              raise uu____3493
          | M uu____3502 ->
              let uu____3503 = check env1 e2 context_nm in strip_m uu____3503 in
        let uu____3507 =
          let uu____3508 = FStar_Syntax_Subst.compress e in
          uu____3508.FStar_Syntax_Syntax.n in
        match uu____3507 with
        | FStar_Syntax_Syntax.Tm_bvar uu____3514 ->
            let uu____3515 = infer env e in return_if uu____3515
        | FStar_Syntax_Syntax.Tm_name uu____3519 ->
            let uu____3520 = infer env e in return_if uu____3520
        | FStar_Syntax_Syntax.Tm_fvar uu____3524 ->
            let uu____3525 = infer env e in return_if uu____3525
        | FStar_Syntax_Syntax.Tm_abs uu____3529 ->
            let uu____3544 = infer env e in return_if uu____3544
        | FStar_Syntax_Syntax.Tm_constant uu____3548 ->
            let uu____3549 = infer env e in return_if uu____3549
        | FStar_Syntax_Syntax.Tm_app uu____3553 ->
            let uu____3563 = infer env e in return_if uu____3563
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____3610) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____3616) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____3622,uu____3623) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____3652 ->
            let uu____3660 =
              let uu____3661 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3661 in
            failwith uu____3660
        | FStar_Syntax_Syntax.Tm_type uu____3665 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3669 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3680 ->
            let uu____3685 =
              let uu____3686 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3686 in
            failwith uu____3685
        | FStar_Syntax_Syntax.Tm_uvar uu____3690 ->
            let uu____3699 =
              let uu____3700 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3700 in
            failwith uu____3699
        | FStar_Syntax_Syntax.Tm_delayed uu____3704 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3728 =
              let uu____3729 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3729 in
            failwith uu____3728
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
      let uu____3751 =
        let uu____3752 = FStar_Syntax_Subst.compress e in
        uu____3752.FStar_Syntax_Syntax.n in
      match uu____3751 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst1 body in
          let env1 =
            let uu___110_3792 = env in
            let uu____3793 =
              FStar_TypeChecker_Env.push_binders env.env binders1 in
            {
              env = uu____3793;
              subst = (uu___110_3792.subst);
              tc_const = (uu___110_3792.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun uu____3802  ->
                 match uu____3802 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort in
                     ((let uu___111_3810 = bv in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___111_3810.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___111_3810.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1 in
          let uu____3811 =
            FStar_List.fold_left
              (fun uu____3820  ->
                 fun uu____3821  ->
                   match (uu____3820, uu____3821) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu____3849 = is_C c in
                       if uu____3849
                       then
                         let xw =
                           let uu____3854 = star_type' env2 c in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") None uu____3854 in
                         let x =
                           let uu___112_3856 = bv in
                           let uu____3857 =
                             let uu____3860 =
                               FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env2 c uu____3860 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___112_3856.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___112_3856.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3857
                           } in
                         let env3 =
                           let uu___113_3862 = env2 in
                           let uu____3863 =
                             let uu____3865 =
                               let uu____3866 =
                                 let uu____3871 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu____3871) in
                               FStar_Syntax_Syntax.NT uu____3866 in
                             uu____3865 :: (env2.subst) in
                           {
                             env = (uu___113_3862.env);
                             subst = uu____3863;
                             tc_const = (uu___113_3862.tc_const)
                           } in
                         let uu____3872 =
                           let uu____3874 = FStar_Syntax_Syntax.mk_binder x in
                           let uu____3875 =
                             let uu____3877 =
                               FStar_Syntax_Syntax.mk_binder xw in
                             uu____3877 :: acc in
                           uu____3874 :: uu____3875 in
                         (env3, uu____3872)
                       else
                         (let x =
                            let uu___114_3881 = bv in
                            let uu____3882 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_3881.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_3881.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3882
                            } in
                          let uu____3885 =
                            let uu____3887 = FStar_Syntax_Syntax.mk_binder x in
                            uu____3887 :: acc in
                          (env2, uu____3885))) (env1, []) binders1 in
          (match uu____3811 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu____3899 =
                 let check_what =
                   let uu____3911 = is_monadic what in
                   if uu____3911 then check_m else check_n in
                 let uu____3920 = check_what env2 body1 in
                 match uu____3920 with
                 | (t,s_body,u_body) ->
                     let uu____3930 =
                       let uu____3931 =
                         let uu____3932 = is_monadic what in
                         if uu____3932 then M t else N t in
                       comp_of_nm uu____3931 in
                     (uu____3930, s_body, u_body) in
               (match uu____3899 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3975 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___96_3977  ->
                                    match uu___96_3977 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3978 -> false)) in
                          if uu____3975
                          then
                            let double_starred_comp =
                              let uu____3986 =
                                let uu____3987 =
                                  let uu____3988 =
                                    lc.FStar_Syntax_Syntax.comp () in
                                  FStar_Syntax_Util.comp_result uu____3988 in
                                FStar_All.pipe_left double_star uu____3987 in
                              FStar_Syntax_Syntax.mk_Total uu____3986 in
                            let flags =
                              FStar_List.filter
                                (fun uu___97_3993  ->
                                   match uu___97_3993 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3994 -> true)
                                lc.FStar_Syntax_Syntax.cflags in
                            let uu____3995 =
                              let uu____4001 =
                                let uu____4002 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags in
                                FStar_Syntax_Util.lcomp_of_comp uu____4002 in
                              FStar_Util.Inl uu____4001 in
                            Some uu____3995
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___115_4022 = lc in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___115_4022.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___115_4022.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___115_4022.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____4023  ->
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
                          let uu____4040 =
                            let uu____4046 =
                              let uu____4050 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___98_4052  ->
                                        match uu___98_4052 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____4053 -> false)) in
                              if uu____4050
                              then
                                let uu____4057 =
                                  FStar_List.filter
                                    (fun uu___99_4059  ->
                                       match uu___99_4059 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____4060 -> true) flags in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____4057)
                              else (lid, flags) in
                            FStar_Util.Inr uu____4046 in
                          Some uu____4040 in
                    let uu____4072 =
                      let comp1 =
                        let uu____4084 = is_monadic what in
                        let uu____4085 =
                          FStar_Syntax_Subst.subst env2.subst s_body in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____4084 uu____4085 in
                      let uu____4086 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None) in
                      (uu____4086,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1)))) in
                    (match uu____4072 with
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
                FStar_Syntax_Syntax.ty = uu____4164;
                FStar_Syntax_Syntax.p = uu____4165;_};
            FStar_Syntax_Syntax.fv_delta = uu____4166;
            FStar_Syntax_Syntax.fv_qual = uu____4167;_}
          ->
          let uu____4173 =
            let uu____4176 = FStar_TypeChecker_Env.lookup_lid env.env lid in
            FStar_All.pipe_left FStar_Pervasives.fst uu____4176 in
          (match uu____4173 with
           | (uu____4192,t) ->
               let uu____4194 = let uu____4195 = normalize1 t in N uu____4195 in
               (uu____4194, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4212 = check_n env head1 in
          (match uu____4212 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4226 =
                   let uu____4227 = FStar_Syntax_Subst.compress t in
                   uu____4227.FStar_Syntax_Syntax.n in
                 match uu____4226 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4230 -> true
                 | uu____4238 -> false in
               let rec flatten1 t =
                 let uu____4250 =
                   let uu____4251 = FStar_Syntax_Subst.compress t in
                   uu____4251.FStar_Syntax_Syntax.n in
                 match uu____4250 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4263);
                                FStar_Syntax_Syntax.tk = uu____4264;
                                FStar_Syntax_Syntax.pos = uu____4265;
                                FStar_Syntax_Syntax.vars = uu____4266;_})
                     when is_arrow t1 ->
                     let uu____4283 = flatten1 t1 in
                     (match uu____4283 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4335,uu____4336)
                     -> flatten1 e1
                 | uu____4365 ->
                     let uu____4366 =
                       let uu____4367 =
                         let uu____4368 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4368 in
                       FStar_Errors.Err uu____4367 in
                     raise uu____4366 in
               let uu____4376 = flatten1 t_head in
               (match uu____4376 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4428 =
                          let uu____4429 =
                            let uu____4430 = FStar_Util.string_of_int n1 in
                            let uu____4437 =
                              FStar_Util.string_of_int (n' - n1) in
                            let uu____4448 = FStar_Util.string_of_int n1 in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4430 uu____4437 uu____4448 in
                          FStar_Errors.Err uu____4429 in
                        raise uu____4428)
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
                           | (binders2,uu____4664) ->
                               let uu____4677 =
                                 let uu____4687 =
                                   FStar_List.map2
                                     (fun uu____4707  ->
                                        fun uu____4708  ->
                                          match (uu____4707, uu____4708) with
                                          | ((bv,uu____4725),(arg,q)) ->
                                              let uu____4732 =
                                                let uu____4733 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu____4733.FStar_Syntax_Syntax.n in
                                              (match uu____4732 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4743 ->
                                                   let arg1 = (arg, q) in
                                                   (arg1, [arg1])
                                               | uu____4756 ->
                                                   let uu____4757 =
                                                     check_n env arg in
                                                   (match uu____4757 with
                                                    | (uu____4768,s_arg,u_arg)
                                                        ->
                                                        let uu____4771 =
                                                          let uu____4775 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu____4775
                                                          then
                                                            let uu____4779 =
                                                              let uu____4782
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg in
                                                              (uu____4782, q) in
                                                            [uu____4779;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q),
                                                          uu____4771))))
                                     binders2 args in
                                 FStar_List.split uu____4687 in
                               (match uu____4677 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu____4829 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu____4835 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu____4829, uu____4835)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4884) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____4890) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4896,uu____4897) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4927 = let uu____4928 = env.tc_const c in N uu____4928 in
          (uu____4927, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4929 ->
          let uu____4937 =
            let uu____4938 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4938 in
          failwith uu____4937
      | FStar_Syntax_Syntax.Tm_type uu____4942 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4946 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4957 ->
          let uu____4962 =
            let uu____4963 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4963 in
          failwith uu____4962
      | FStar_Syntax_Syntax.Tm_uvar uu____4967 ->
          let uu____4976 =
            let uu____4977 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4977 in
          failwith uu____4976
      | FStar_Syntax_Syntax.Tm_delayed uu____4981 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____5005 =
            let uu____5006 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____5006 in
          failwith uu____5005
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
          let uu____5044 = check_n env e0 in
          match uu____5044 with
          | (uu____5051,s_e0,u_e0) ->
              let uu____5054 =
                let uu____5072 =
                  FStar_List.map
                    (fun b  ->
                       let uu____5105 = FStar_Syntax_Subst.open_branch b in
                       match uu____5105 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___116_5137 = env in
                             let uu____5138 =
                               let uu____5139 =
                                 FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____5139 in
                             {
                               env = uu____5138;
                               subst = (uu___116_5137.subst);
                               tc_const = (uu___116_5137.tc_const)
                             } in
                           let uu____5141 = f env1 body in
                           (match uu____5141 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____5190 ->
                           raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu____5072 in
              (match uu____5054 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5255 = FStar_List.hd nms in
                     match uu____5255 with | M t1 -> t1 | N t1 -> t1 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___100_5259  ->
                          match uu___100_5259 with
                          | M uu____5260 -> true
                          | uu____5261 -> false) nms in
                   let uu____5262 =
                     let uu____5285 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5337  ->
                              match uu____5337 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5460 =
                                         check env original_body (M t2) in
                                       (match uu____5460 with
                                        | (uu____5483,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5512,false ) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu____5285 in
                   (match uu____5262 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5631  ->
                                 match uu____5631 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5672 =
                                         let uu____5673 =
                                           let uu____5683 =
                                             let uu____5687 =
                                               let uu____5690 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu____5691 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu____5690, uu____5691) in
                                             [uu____5687] in
                                           (s_body, uu____5683) in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5673 in
                                       mk1 uu____5672 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu____5713 =
                              let uu____5714 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____5714] in
                            let uu____5715 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2)) in
                            let uu____5717 =
                              let uu____5724 =
                                let uu____5730 =
                                  let uu____5731 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5731 in
                                FStar_Util.Inl uu____5730 in
                              Some uu____5724 in
                            FStar_Syntax_Util.abs uu____5713 uu____5715
                              uu____5717 in
                          let t1_star =
                            let uu____5745 =
                              let uu____5749 =
                                let uu____5750 =
                                  FStar_Syntax_Syntax.new_bv None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5750 in
                              [uu____5749] in
                            let uu____5751 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu____5745 uu____5751 in
                          let uu____5754 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None)) in
                          let uu____5784 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1)) in
                          ((M t1), uu____5754, uu____5784)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu____5798 =
                             let uu____5801 =
                               let uu____5802 =
                                 let uu____5820 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1)) in
                                 (uu____5820,
                                   ((FStar_Util.Inl t1_star), None), None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5802 in
                             mk1 uu____5801 in
                           let uu____5847 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1)) in
                           ((N t1), uu____5798, uu____5847))))
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
              let uu____5890 = FStar_Syntax_Syntax.mk_binder x in
              [uu____5890] in
            let uu____5891 = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu____5891 with
            | (x_binders1,e21) ->
                let uu____5899 = infer env e1 in
                (match uu____5899 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5910 = is_C t1 in
                       if uu____5910
                       then
                         let uu___117_5911 = binding in
                         let uu____5912 =
                           let uu____5915 =
                             FStar_Syntax_Subst.subst env.subst s_e1 in
                           trans_F_ env t1 uu____5915 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___117_5911.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___117_5911.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5912;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___117_5911.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___117_5911.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding in
                     let env1 =
                       let uu___118_5918 = env in
                       let uu____5919 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5920 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5920.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5920.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5919;
                         subst = (uu___118_5918.subst);
                         tc_const = (uu___118_5918.tc_const)
                       } in
                     let uu____5921 = proceed env1 e21 in
                     (match uu____5921 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___120_5932 = binding in
                            let uu____5933 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___120_5932.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___120_5932.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5933;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___120_5932.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___120_5932.FStar_Syntax_Syntax.lbdef)
                            } in
                          let uu____5936 =
                            let uu____5939 =
                              let uu____5940 =
                                let uu____5948 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___121_5953 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___121_5953.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___121_5953.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___121_5953.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___121_5953.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5948) in
                              FStar_Syntax_Syntax.Tm_let uu____5940 in
                            mk1 uu____5939 in
                          let uu____5954 =
                            let uu____5957 =
                              let uu____5958 =
                                let uu____5966 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___122_5971 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_5971.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_5971.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_5971.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_5971.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5966) in
                              FStar_Syntax_Syntax.Tm_let uu____5958 in
                            mk1 uu____5957 in
                          (nm_rec, uu____5936, uu____5954))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___123_5980 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___123_5980.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___123_5980.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___123_5980.FStar_Syntax_Syntax.lbdef)
                       } in
                     let env1 =
                       let uu___124_5982 = env in
                       let uu____5983 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___125_5984 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_5984.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_5984.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         env = uu____5983;
                         subst = (uu___124_5982.subst);
                         tc_const = (uu___124_5982.tc_const)
                       } in
                     let uu____5985 = ensure_m env1 e21 in
                     (match uu____5985 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type in
                          let s_e21 =
                            let uu____6002 =
                              let uu____6003 =
                                let uu____6013 =
                                  let uu____6017 =
                                    let uu____6020 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu____6021 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6020, uu____6021) in
                                  [uu____6017] in
                                (s_e2, uu____6013) in
                              FStar_Syntax_Syntax.Tm_app uu____6003 in
                            mk1 uu____6002 in
                          let s_e22 =
                            let uu____6030 =
                              let uu____6037 =
                                let uu____6043 =
                                  let uu____6044 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6044 in
                                FStar_Util.Inl uu____6043 in
                              Some uu____6037 in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____6030 in
                          let body =
                            let uu____6058 =
                              let uu____6059 =
                                let uu____6069 =
                                  let uu____6073 =
                                    let uu____6076 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu____6076) in
                                  [uu____6073] in
                                (s_e1, uu____6069) in
                              FStar_Syntax_Syntax.Tm_app uu____6059 in
                            mk1 uu____6058 in
                          let uu____6084 =
                            let uu____6085 =
                              let uu____6086 =
                                FStar_Syntax_Syntax.mk_binder p in
                              [uu____6086] in
                            let uu____6087 =
                              let uu____6094 =
                                let uu____6100 =
                                  let uu____6101 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0 in
                                  FStar_Syntax_Util.lcomp_of_comp uu____6101 in
                                FStar_Util.Inl uu____6100 in
                              Some uu____6094 in
                            FStar_Syntax_Util.abs uu____6085 body uu____6087 in
                          let uu____6112 =
                            let uu____6115 =
                              let uu____6116 =
                                let uu____6124 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___126_6129 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___126_6129.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___126_6129.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___126_6129.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___126_6129.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____6124) in
                              FStar_Syntax_Syntax.Tm_let uu____6116 in
                            mk1 uu____6115 in
                          ((M t2), uu____6084, uu____6112)))
and check_n:
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____6138 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos in
        N uu____6138 in
      let uu____6143 = check env e mn in
      match uu____6143 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6153 -> failwith "[check_n]: impossible"
and check_m:
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
        M uu____6166 in
      let uu____6171 = check env e mn in
      match uu____6171 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____6181 -> failwith "[check_m]: impossible"
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
        (let uu____6203 =
           let uu____6204 = is_C c in Prims.op_Negation uu____6204 in
         if uu____6203 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos in
         let uu____6216 =
           let uu____6217 = FStar_Syntax_Subst.compress c in
           uu____6217.FStar_Syntax_Syntax.n in
         match uu____6216 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6236 = FStar_Syntax_Util.head_and_args wp in
             (match uu____6236 with
              | (wp_head,wp_args) ->
                  ((let uu____6263 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6280 =
                           let uu____6281 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6281 in
                         Prims.op_Negation uu____6280) in
                    if uu____6263 then failwith "mismatch" else ());
                   (let uu____6293 =
                      let uu____6294 =
                        let uu____6304 =
                          FStar_List.map2
                            (fun uu____6314  ->
                               fun uu____6315  ->
                                 match (uu____6314, uu____6315) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6338 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu____6338
                                       then "implicit"
                                       else "explicit" in
                                     (if q <> q'
                                      then
                                        (let uu____6341 = print_implicit q in
                                         let uu____6342 = print_implicit q' in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6341 uu____6342)
                                      else ();
                                      (let uu____6344 =
                                         trans_F_ env arg wp_arg in
                                       (uu____6344, q)))) args wp_args in
                        (head1, uu____6304) in
                      FStar_Syntax_Syntax.Tm_app uu____6294 in
                    mk1 uu____6293)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu____6366 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu____6366 with
              | (binders_orig,comp1) ->
                  let uu____6371 =
                    let uu____6379 =
                      FStar_List.map
                        (fun uu____6393  ->
                           match uu____6393 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu____6406 = is_C h in
                               if uu____6406
                               then
                                 let w' =
                                   let uu____6413 = star_type' env h in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") None uu____6413 in
                                 let uu____6414 =
                                   let uu____6418 =
                                     let uu____6422 =
                                       let uu____6425 =
                                         let uu____6426 =
                                           let uu____6427 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env h uu____6427 in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6426 in
                                       (uu____6425, q) in
                                     [uu____6422] in
                                   (w', q) :: uu____6418 in
                                 (w', uu____6414)
                               else
                                 (let x =
                                    let uu____6439 = star_type' env h in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") None uu____6439 in
                                  (x, [(x, q)]))) binders_orig in
                    FStar_List.split uu____6379 in
                  (match uu____6371 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu____6469 =
                           let uu____6471 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6471 in
                         FStar_Syntax_Subst.subst_comp uu____6469 comp1 in
                       let app =
                         let uu____6475 =
                           let uu____6476 =
                             let uu____6486 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6493 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu____6494 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu____6493, uu____6494)) bvs in
                             (wp, uu____6486) in
                           FStar_Syntax_Syntax.Tm_app uu____6476 in
                         mk1 uu____6475 in
                       let comp3 =
                         let uu____6499 = type_of_comp comp2 in
                         let uu____6500 = is_monadic_comp comp2 in
                         trans_G env uu____6499 uu____6500 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6502,uu____6503) ->
             trans_F_ env e wp
         | uu____6532 -> failwith "impossible trans_F_")
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
            let uu____6537 =
              let uu____6538 = star_type' env h in
              let uu____6541 =
                let uu____6547 =
                  let uu____6550 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu____6550) in
                [uu____6547] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6538;
                FStar_Syntax_Syntax.effect_args = uu____6541;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu____6537
          else
            (let uu____6556 = trans_F_ env h wp in
             FStar_Syntax_Syntax.mk_Total uu____6556)
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
    fun t  -> let uu____6571 = n env.env t in star_type' env uu____6571
let star_expr:
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.term*
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6585 = n env.env t in check_n env uu____6585
let trans_F:
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6598 = n env.env c in
        let uu____6599 = n env.env wp in trans_F_ env uu____6598 uu____6599