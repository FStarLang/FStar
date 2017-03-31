open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const } 
let gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___95_64 = a  in
              let uu____65 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___95_64.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___95_64.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65
              }  in
            let d s = FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s  in
            (let uu____73 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____73
             then
               (d "Elaborating extra WP combinators";
                (let uu____75 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____75))
             else ());
            (let rec collect_binders t =
               let uu____84 =
                 let uu____85 =
                   let uu____88 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____88
                    in
                 uu____85.FStar_Syntax_Syntax.n  in
               match uu____84 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____110) -> t1
                     | uu____117 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____120 = collect_binders rest  in
                   FStar_List.append bs uu____120
               | FStar_Syntax_Syntax.Tm_type uu____126 -> []
               | uu____129 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name =
               FStar_Ident.lid_of_path
                 (FStar_Ident.path_of_text
                    (Prims.strcat
                       (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname)
                       (Prims.strcat "_" name))) FStar_Range.dummyRange
                in
             let gamma =
               let uu____141 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____141 FStar_Syntax_Util.name_binders
                in
             (let uu____152 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____152
              then
                let uu____153 =
                  let uu____154 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____154  in
                d uu____153
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                (FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange  in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____186 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____186 with
                | (sigelt,fv) ->
                    ((let uu____192 =
                        let uu____194 = FStar_ST.read sigelts  in sigelt ::
                          uu____194
                         in
                      FStar_ST.write sigelts uu____192);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____215  ->
                     match uu____215 with
                     | (t,b) ->
                         let uu____222 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____222))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____239 = FStar_Syntax_Syntax.as_implicit true  in
                     ((Prims.fst t), uu____239))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____252 =
                       FStar_Syntax_Syntax.bv_to_name (Prims.fst bv)  in
                     FStar_Syntax_Syntax.as_arg uu____252)
                 in
              let uu____253 =
                let uu____265 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____279 = f (FStar_Syntax_Syntax.bv_to_name t)
                         in
                      FStar_Syntax_Util.arrow gamma uu____279  in
                    let uu____280 =
                      let uu____284 =
                        let uu____288 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____289 =
                          let uu____291 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____291]  in
                        uu____288 :: uu____289  in
                      FStar_List.append binders uu____284  in
                    FStar_Syntax_Util.abs uu____280 body None  in
                  let uu____299 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____300 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____299, uu____300)  in
                match uu____265 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____331 =
                        let uu____332 =
                          let uu____342 =
                            let uu____346 =
                              FStar_List.map
                                (fun uu____354  ->
                                   match uu____354 with
                                   | (bv,uu____360) ->
                                       let uu____361 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____362 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____361, uu____362)) binders
                               in
                            let uu____363 =
                              let uu____367 =
                                let uu____370 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____371 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____370, uu____371)  in
                              let uu____372 =
                                let uu____376 =
                                  let uu____379 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____379)  in
                                [uu____376]  in
                              uu____367 :: uu____372  in
                            FStar_List.append uu____346 uu____363  in
                          (fv, uu____342)  in
                        FStar_Syntax_Syntax.Tm_app uu____332  in
                      mk1 uu____331  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____253 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t" None
                        FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____425 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____425  in
                    let ret1 =
                      let uu____433 =
                        let uu____439 =
                          let uu____440 =
                            let uu____441 =
                              let uu____442 =
                                FStar_Syntax_Syntax.bv_to_name t  in
                              mk_ctx uu____442  in
                            FStar_Syntax_Syntax.mk_Total uu____441  in
                          FStar_TypeChecker_Env.lcomp_of_comp env1 uu____440
                           in
                        FStar_Util.Inl uu____439  in
                      Some uu____433  in
                    let body =
                      let uu____452 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____452 ret1  in
                    let uu____453 =
                      let uu____457 = mk_all_implicit binders  in
                      let uu____461 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____457 uu____461  in
                    FStar_Syntax_Util.abs uu____453 body ret1  in
                  let c_pure1 =
                    let uu____476 = mk_lid "pure"  in
                    register env1 uu____476 c_pure  in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let l =
                      let uu____481 =
                        let uu____482 =
                          let uu____483 =
                            let uu____484 =
                              let uu____485 =
                                let uu____486 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv None uu____486  in
                              FStar_Syntax_Syntax.mk_binder uu____485  in
                            [uu____484]  in
                          let uu____487 =
                            let uu____488 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____488  in
                          FStar_Syntax_Util.arrow uu____483 uu____487  in
                        mk_gctx uu____482  in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____481  in
                    let r =
                      let uu____490 =
                        let uu____491 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____491  in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____490  in
                    let ret1 =
                      let uu____499 =
                        let uu____505 =
                          let uu____506 =
                            let uu____507 =
                              let uu____508 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              mk_gctx uu____508  in
                            FStar_Syntax_Syntax.mk_Total uu____507  in
                          FStar_TypeChecker_Env.lcomp_of_comp env1 uu____506
                           in
                        FStar_Util.Inl uu____505  in
                      Some uu____499  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____523 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____526 =
                          let uu____532 =
                            let uu____534 =
                              let uu____535 =
                                let uu____536 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____536
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____535  in
                            [uu____534]  in
                          FStar_List.append gamma_as_args uu____532  in
                        FStar_Syntax_Util.mk_app uu____523 uu____526  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____539 =
                      let uu____543 = mk_all_implicit binders  in
                      let uu____547 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____543 uu____547  in
                    FStar_Syntax_Util.abs uu____539 outer_body ret1  in
                  let c_app1 =
                    let uu____566 = mk_lid "app"  in
                    register env1 uu____566 c_app  in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____571 =
                        let uu____572 =
                          let uu____573 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____573  in
                        [uu____572]  in
                      let uu____574 =
                        let uu____575 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____575  in
                      FStar_Syntax_Util.arrow uu____571 uu____574  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a11 =
                      let uu____578 =
                        let uu____579 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____579  in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____578  in
                    let ret1 =
                      let uu____587 =
                        let uu____593 =
                          let uu____594 =
                            let uu____595 =
                              let uu____596 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              mk_gctx uu____596  in
                            FStar_Syntax_Syntax.mk_Total uu____595  in
                          FStar_TypeChecker_Env.lcomp_of_comp env1 uu____594
                           in
                        FStar_Util.Inl uu____593  in
                      Some uu____587  in
                    let uu____605 =
                      let uu____609 = mk_all_implicit binders  in
                      let uu____613 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____609 uu____613  in
                    let uu____631 =
                      let uu____632 =
                        let uu____638 =
                          let uu____640 =
                            let uu____643 =
                              let uu____649 =
                                let uu____651 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____651]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____649
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____643  in
                          let uu____652 =
                            let uu____656 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____656]  in
                          uu____640 :: uu____652  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____638
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____632  in
                    FStar_Syntax_Util.abs uu____605 uu____631 ret1  in
                  let c_lift11 =
                    let uu____660 = mk_lid "lift1"  in
                    register env1 uu____660 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____666 =
                        let uu____667 =
                          let uu____668 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____668  in
                        let uu____669 =
                          let uu____671 =
                            let uu____672 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.null_binder uu____672  in
                          [uu____671]  in
                        uu____667 :: uu____669  in
                      let uu____673 =
                        let uu____674 = FStar_Syntax_Syntax.bv_to_name t3  in
                        FStar_Syntax_Syntax.mk_GTotal uu____674  in
                      FStar_Syntax_Util.arrow uu____666 uu____673  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a11 =
                      let uu____677 =
                        let uu____678 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____678  in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____677  in
                    let a2 =
                      let uu____680 =
                        let uu____681 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____681  in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____680  in
                    let ret1 =
                      let uu____689 =
                        let uu____695 =
                          let uu____696 =
                            let uu____697 =
                              let uu____698 =
                                FStar_Syntax_Syntax.bv_to_name t3  in
                              mk_gctx uu____698  in
                            FStar_Syntax_Syntax.mk_Total uu____697  in
                          FStar_TypeChecker_Env.lcomp_of_comp env1 uu____696
                           in
                        FStar_Util.Inl uu____695  in
                      Some uu____689  in
                    let uu____707 =
                      let uu____711 = mk_all_implicit binders  in
                      let uu____715 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____711 uu____715  in
                    let uu____737 =
                      let uu____738 =
                        let uu____744 =
                          let uu____746 =
                            let uu____749 =
                              let uu____755 =
                                let uu____757 =
                                  let uu____760 =
                                    let uu____766 =
                                      let uu____768 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____768]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____766
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____760
                                   in
                                let uu____769 =
                                  let uu____773 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____773]  in
                                uu____757 :: uu____769  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____755
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____749  in
                          let uu____776 =
                            let uu____780 = FStar_Syntax_Syntax.bv_to_name a2
                               in
                            [uu____780]  in
                          uu____746 :: uu____776  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____744
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____738  in
                    FStar_Syntax_Util.abs uu____707 uu____737 ret1  in
                  let c_lift21 =
                    let uu____784 = mk_lid "lift2"  in
                    register env1 uu____784 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1" None
                        FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____789 =
                        let uu____790 =
                          let uu____791 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____791  in
                        [uu____790]  in
                      let uu____792 =
                        let uu____793 =
                          let uu____794 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____794  in
                        FStar_Syntax_Syntax.mk_Total uu____793  in
                      FStar_Syntax_Util.arrow uu____789 uu____792  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let ret1 =
                      let uu____803 =
                        let uu____809 =
                          let uu____810 =
                            let uu____811 =
                              let uu____812 =
                                let uu____813 =
                                  let uu____814 =
                                    let uu____815 =
                                      FStar_Syntax_Syntax.bv_to_name t1  in
                                    FStar_Syntax_Syntax.null_binder uu____815
                                     in
                                  [uu____814]  in
                                let uu____816 =
                                  let uu____817 =
                                    FStar_Syntax_Syntax.bv_to_name t2  in
                                  FStar_Syntax_Syntax.mk_GTotal uu____817  in
                                FStar_Syntax_Util.arrow uu____813 uu____816
                                 in
                              mk_ctx uu____812  in
                            FStar_Syntax_Syntax.mk_Total uu____811  in
                          FStar_TypeChecker_Env.lcomp_of_comp env1 uu____810
                           in
                        FStar_Util.Inl uu____809  in
                      Some uu____803  in
                    let e1 =
                      let uu____827 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____827  in
                    let body =
                      let uu____829 =
                        let uu____833 =
                          let uu____837 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____837]  in
                        FStar_List.append gamma uu____833  in
                      let uu____840 =
                        let uu____841 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____844 =
                          let uu____850 =
                            let uu____851 = FStar_Syntax_Syntax.bv_to_name e1
                               in
                            FStar_Syntax_Syntax.as_arg uu____851  in
                          let uu____852 = args_of_binders1 gamma  in
                          uu____850 :: uu____852  in
                        FStar_Syntax_Util.mk_app uu____841 uu____844  in
                      FStar_Syntax_Util.abs uu____829 uu____840 ret1  in
                    let uu____854 =
                      let uu____858 = mk_all_implicit binders  in
                      let uu____862 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____858 uu____862  in
                    FStar_Syntax_Util.abs uu____854 body ret1  in
                  let c_push1 =
                    let uu____879 = mk_lid "push"  in
                    register env1 uu____879 c_push  in
                  let ret_tot_wp_a =
                    let uu____887 =
                      let uu____893 =
                        let uu____894 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_TypeChecker_Env.lcomp_of_comp env1 uu____894
                         in
                      FStar_Util.Inl uu____893  in
                    Some uu____887  in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____920 =
                        let uu____921 =
                          let uu____931 = args_of_binders1 binders  in
                          (c, uu____931)  in
                        FStar_Syntax_Syntax.Tm_app uu____921  in
                      mk1 uu____920
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____939 =
                        let uu____940 =
                          let uu____941 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____942 =
                            let uu____944 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____944]  in
                          uu____941 :: uu____942  in
                        let uu____945 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____940 uu____945  in
                      FStar_Syntax_Syntax.mk_Total uu____939  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype
                       in
                    let uu____947 =
                      let uu____951 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____951  in
                    let uu____957 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None
                         in
                      let uu____959 =
                        let uu____962 =
                          let uu____968 =
                            let uu____970 =
                              let uu____973 =
                                let uu____979 =
                                  let uu____980 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____980  in
                                [uu____979]  in
                              FStar_Syntax_Util.mk_app l_ite uu____973  in
                            [uu____970]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg uu____968
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____962  in
                      FStar_Syntax_Util.ascribe uu____959
                        (FStar_Util.Inr result_comp)
                       in
                    let uu____987 =
                      let uu____994 =
                        let uu____1000 =
                          FStar_TypeChecker_Env.lcomp_of_comp env1
                            result_comp
                           in
                        FStar_Util.Inl uu____1000  in
                      Some uu____994  in
                    FStar_Syntax_Util.abs uu____947 uu____957 uu____987  in
                  let wp_if_then_else1 =
                    let uu____1010 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1010 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q" None
                        FStar_Syntax_Util.ktype
                       in
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1")) None
                       in
                    let body =
                      let uu____1021 =
                        let uu____1027 =
                          let uu____1029 =
                            let uu____1032 =
                              let uu____1038 =
                                let uu____1040 =
                                  let uu____1043 =
                                    let uu____1049 =
                                      let uu____1050 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1050
                                       in
                                    [uu____1049]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1043
                                   in
                                [uu____1040]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1038
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1032  in
                          let uu____1055 =
                            let uu____1059 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1059]  in
                          uu____1029 :: uu____1055  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1027
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1021  in
                    let uu____1062 =
                      let uu____1066 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1066  in
                    FStar_Syntax_Util.abs uu____1062 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1073 = mk_lid "wp_assert"  in
                    register env1 uu____1073 wp_assert  in
                  let wp_assert2 = mk_generic_app wp_assert1  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q" None
                        FStar_Syntax_Util.ktype
                       in
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "1")) None
                       in
                    let body =
                      let uu____1084 =
                        let uu____1090 =
                          let uu____1092 =
                            let uu____1095 =
                              let uu____1101 =
                                let uu____1103 =
                                  let uu____1106 =
                                    let uu____1112 =
                                      let uu____1113 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1113
                                       in
                                    [uu____1112]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1106
                                   in
                                [uu____1103]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1101
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1095  in
                          let uu____1118 =
                            let uu____1122 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1122]  in
                          uu____1092 :: uu____1118  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1090
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1084  in
                    let uu____1125 =
                      let uu____1129 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1129  in
                    FStar_Syntax_Util.abs uu____1125 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1136 = mk_lid "wp_assume"  in
                    register env1 uu____1136 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1143 =
                        let uu____1144 =
                          let uu____1145 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1145  in
                        [uu____1144]  in
                      let uu____1146 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1143 uu____1146  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let body =
                      let uu____1151 =
                        let uu____1157 =
                          let uu____1159 =
                            let uu____1162 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1162  in
                          let uu____1168 =
                            let uu____1172 =
                              let uu____1175 =
                                let uu____1181 =
                                  let uu____1183 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1183]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1181
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1175  in
                            [uu____1172]  in
                          uu____1159 :: uu____1168  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1157
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1151  in
                    let uu____1190 =
                      let uu____1194 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1194  in
                    FStar_Syntax_Util.abs uu____1190 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1201 = mk_lid "wp_close"  in
                    register env1 uu____1201 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    let uu____1212 =
                      let uu____1218 =
                        let uu____1219 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.lcomp_of_comp env1)
                          uu____1219
                         in
                      FStar_Util.Inl uu____1218  in
                    Some uu____1212  in
                  let ret_gtot_type =
                    let uu____1235 =
                      let uu____1241 =
                        let uu____1242 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.lcomp_of_comp env1)
                          uu____1242
                         in
                      FStar_Util.Inl uu____1241  in
                    Some uu____1235  in
                  let mk_forall1 x body =
                    let uu____1258 =
                      let uu____1261 =
                        let uu____1262 =
                          let uu____1272 =
                            let uu____1274 =
                              let uu____1275 =
                                let uu____1276 =
                                  let uu____1280 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1280]  in
                                FStar_Syntax_Util.abs uu____1276 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1275  in
                            [uu____1274]  in
                          (FStar_Syntax_Util.tforall, uu____1272)  in
                        FStar_Syntax_Syntax.Tm_app uu____1262  in
                      FStar_Syntax_Syntax.mk uu____1261  in
                    uu____1258 None FStar_Range.dummyRange  in
                  let rec is_discrete t =
                    let uu____1294 =
                      let uu____1295 = FStar_Syntax_Subst.compress t  in
                      uu____1295.FStar_Syntax_Syntax.n  in
                    match uu____1294 with
                    | FStar_Syntax_Syntax.Tm_type uu____1298 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1313  ->
                              match uu____1313 with
                              | (b,uu____1317) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          &&
                          (let uu____1318 =
                             FStar_TypeChecker_Env.result_typ env1 c  in
                           is_discrete uu____1318)
                    | uu____1319 -> true  in
                  let rec is_monotonic t =
                    let uu____1324 =
                      let uu____1325 = FStar_Syntax_Subst.compress t  in
                      uu____1325.FStar_Syntax_Syntax.n  in
                    match uu____1324 with
                    | FStar_Syntax_Syntax.Tm_type uu____1328 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1343  ->
                              match uu____1343 with
                              | (b,uu____1347) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          &&
                          (let uu____1348 =
                             FStar_TypeChecker_Env.result_typ env1 c  in
                           is_monotonic uu____1348)
                    | uu____1349 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1401 =
                      let uu____1402 = FStar_Syntax_Subst.compress t1  in
                      uu____1402.FStar_Syntax_Syntax.n  in
                    match uu____1401 with
                    | FStar_Syntax_Syntax.Tm_type uu____1405 -> rel x y
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
                        let a2 = (Prims.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1451 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1451
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2
                             in
                          let body =
                            let uu____1454 =
                              let uu____1457 =
                                let uu____1463 =
                                  let uu____1464 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1464  in
                                [uu____1463]  in
                              FStar_Syntax_Util.mk_app x uu____1457  in
                            let uu____1465 =
                              let uu____1468 =
                                let uu____1474 =
                                  let uu____1475 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1475  in
                                [uu____1474]  in
                              FStar_Syntax_Util.mk_app y uu____1468  in
                            mk_rel1 b uu____1454 uu____1465  in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2
                              in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2
                              in
                           let body =
                             let uu____1480 =
                               let uu____1481 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1484 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1481 uu____1484  in
                             let uu____1487 =
                               let uu____1488 =
                                 let uu____1491 =
                                   let uu____1497 =
                                     let uu____1498 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1498
                                      in
                                   [uu____1497]  in
                                 FStar_Syntax_Util.mk_app x uu____1491  in
                               let uu____1499 =
                                 let uu____1502 =
                                   let uu____1508 =
                                     let uu____1509 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1509
                                      in
                                   [uu____1508]  in
                                 FStar_Syntax_Util.mk_app y uu____1502  in
                               mk_rel1 b uu____1488 uu____1499  in
                             FStar_Syntax_Util.mk_imp uu____1480 uu____1487
                              in
                           let uu____1510 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1510)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___96_1531 = t1  in
                          let uu____1532 =
                            let uu____1533 =
                              let uu____1541 =
                                let uu____1542 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____1542  in
                              ([binder], uu____1541)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____1533  in
                          {
                            FStar_Syntax_Syntax.n = uu____1532;
                            FStar_Syntax_Syntax.tk =
                              (uu___96_1531.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___96_1531.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___96_1531.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1554 ->
                        failwith "unhandled arrow"
                    | uu____1562 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 = FStar_Syntax_Syntax.gen_bv "wp1" None wp_a1  in
                    let wp2 = FStar_Syntax_Syntax.gen_bv "wp2" None wp_a1  in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] env1 t
                         in
                      let uu____1577 =
                        let uu____1578 = FStar_Syntax_Subst.compress t1  in
                        uu____1578.FStar_Syntax_Syntax.n  in
                      match uu____1577 with
                      | FStar_Syntax_Syntax.Tm_type uu____1581 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1598 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____1598
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1613 =
                                let uu____1614 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1614 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____1613
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)]
                             in
                          let uu____1635 =
                            let uu____1639 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1644  ->
                                     match uu____1644 with
                                     | (t2,q) ->
                                         let uu____1649 = project i x  in
                                         let uu____1650 = project i y  in
                                         mk_stronger t2 uu____1649 uu____1650)
                                args
                               in
                            match uu____1639 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____1635 with
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
                                 fun uu____1706  ->
                                   match uu____1706 with
                                   | (bv,q) ->
                                       let uu____1711 =
                                         let uu____1712 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____1712  in
                                       FStar_Syntax_Syntax.gen_bv uu____1711
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1716 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____1716) bvs
                             in
                          let body =
                            let uu____1718 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____1719 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____1718 uu____1719  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1722 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____1724 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____1725 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____1726 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____1724 uu____1725 uu____1726  in
                    let uu____1727 =
                      let uu____1731 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____1731  in
                    FStar_Syntax_Util.abs uu____1727 body ret_tot_type  in
                  let stronger1 =
                    let uu____1746 = mk_lid "stronger"  in
                    register env1 uu____1746 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let uu____1752 = FStar_Util.prefix gamma  in
                    match uu____1752 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (Prims.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____1778 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1778
                             in
                          let uu____1781 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____1781 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1789 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____1789  in
                              let guard_free1 =
                                let uu____1796 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____1796  in
                              let pat =
                                let uu____1800 =
                                  let uu____1806 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____1806]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1800
                                 in
                              let pattern_guarded_body =
                                let uu____1810 =
                                  let uu____1811 =
                                    let uu____1816 =
                                      let uu____1817 =
                                        let uu____1824 =
                                          let uu____1826 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____1826]  in
                                        [uu____1824]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1817
                                       in
                                    (body, uu____1816)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____1811  in
                                mk1 uu____1810  in
                              FStar_Syntax_Util.close_forall binders1
                                pattern_guarded_body
                          | uu____1829 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____1832 =
                            let uu____1833 =
                              let uu____1834 =
                                let uu____1835 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____1838 =
                                  let uu____1844 = args_of_binders1 wp_args
                                     in
                                  let uu____1846 =
                                    let uu____1848 =
                                      let uu____1849 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____1849
                                       in
                                    [uu____1848]  in
                                  FStar_List.append uu____1844 uu____1846  in
                                FStar_Syntax_Util.mk_app uu____1835
                                  uu____1838
                                 in
                              FStar_Syntax_Util.mk_imp equiv uu____1834  in
                            FStar_Syntax_Util.mk_forall k uu____1833  in
                          FStar_Syntax_Util.abs gamma uu____1832
                            ret_gtot_type
                           in
                        let uu____1850 =
                          let uu____1854 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____1854  in
                        FStar_Syntax_Util.abs uu____1850 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____1861 = mk_lid "wp_ite"  in
                    register env1 uu____1861 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let uu____1867 = FStar_Util.prefix gamma  in
                    match uu____1867 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____1891 =
                            let uu____1892 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (Prims.fst post)
                               in
                            let uu____1895 =
                              let uu____1901 =
                                let uu____1902 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____1902  in
                              [uu____1901]  in
                            FStar_Syntax_Util.mk_app uu____1892 uu____1895
                             in
                          FStar_Syntax_Util.mk_forall x uu____1891  in
                        let uu____1903 =
                          let uu____1907 =
                            let uu____1911 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____1911 gamma  in
                          FStar_List.append binders uu____1907  in
                        FStar_Syntax_Util.abs uu____1903 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____1920 = mk_lid "null_wp"  in
                    register env1 uu____1920 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let body =
                      let uu____1929 =
                        let uu____1935 =
                          let uu____1937 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____1938 =
                            let uu____1940 =
                              let uu____1943 =
                                let uu____1949 =
                                  let uu____1950 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____1950  in
                                [uu____1949]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1943
                               in
                            let uu____1951 =
                              let uu____1955 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____1955]  in
                            uu____1940 :: uu____1951  in
                          uu____1937 :: uu____1938  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1935
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____1929  in
                    let uu____1958 =
                      let uu____1962 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____1962  in
                    FStar_Syntax_Util.abs uu____1958 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____1969 = mk_lid "wp_trivial"  in
                    register env1 uu____1969 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____1974 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____1974
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____1979 =
                      let uu____1981 = FStar_ST.read sigelts  in
                      FStar_List.rev uu____1981  in
                    let uu____1986 =
                      let uu___97_1987 = ed  in
                      let uu____1988 =
                        let uu____1989 = c wp_if_then_else2  in
                        ([], uu____1989)  in
                      let uu____1991 =
                        let uu____1992 = c wp_ite2  in ([], uu____1992)  in
                      let uu____1994 =
                        let uu____1995 = c stronger2  in ([], uu____1995)  in
                      let uu____1997 =
                        let uu____1998 = c wp_close2  in ([], uu____1998)  in
                      let uu____2000 =
                        let uu____2001 = c wp_assert2  in ([], uu____2001)
                         in
                      let uu____2003 =
                        let uu____2004 = c wp_assume2  in ([], uu____2004)
                         in
                      let uu____2006 =
                        let uu____2007 = c null_wp2  in ([], uu____2007)  in
                      let uu____2009 =
                        let uu____2010 = c wp_trivial2  in ([], uu____2010)
                         in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___97_1987.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___97_1987.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___97_1987.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___97_1987.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___97_1987.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___97_1987.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___97_1987.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___97_1987.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____1988;
                        FStar_Syntax_Syntax.ite_wp = uu____1991;
                        FStar_Syntax_Syntax.stronger = uu____1994;
                        FStar_Syntax_Syntax.close_wp = uu____1997;
                        FStar_Syntax_Syntax.assert_p = uu____2000;
                        FStar_Syntax_Syntax.assume_p = uu____2003;
                        FStar_Syntax_Syntax.null_wp = uu____2006;
                        FStar_Syntax_Syntax.trivial = uu____2009;
                        FStar_Syntax_Syntax.repr =
                          (uu___97_1987.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___97_1987.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___97_1987.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___97_1987.FStar_Syntax_Syntax.actions)
                      }  in
                    (uu____1979, uu____1986)))))
  
type env_ = env
let get_env : env -> FStar_TypeChecker_Env.env = fun env  -> env.env 
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let uu___is_N : nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2026 -> false 
let __proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0 
let uu___is_M : nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2038 -> false 
let __proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let nm_of_comp : FStar_Syntax_Syntax.comp' -> nm =
  fun uu___84_2048  ->
    match uu___84_2048 with
    | FStar_Syntax_Syntax.Total (t,uu____2050) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___83_2059  ->
                match uu___83_2059 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2060 -> false))
        ->
        let uu____2061 =
          let uu____2062 = FStar_List.hd c.FStar_Syntax_Syntax.effect_args
             in
          Prims.fst uu____2062  in
        M uu____2061
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2074 =
          let uu____2075 =
            let uu____2076 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2076
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2075  in
        failwith uu____2074
    | FStar_Syntax_Syntax.GTotal uu____2077 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let string_of_nm : nm -> Prims.string =
  fun uu___85_2085  ->
    match uu___85_2085 with
    | N t ->
        let uu____2087 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2087
    | M t ->
        let uu____2089 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2089
  
let is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2093,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2095;
                      FStar_Syntax_Syntax.pos = uu____2096;
                      FStar_Syntax_Syntax.vars = uu____2097;_})
        -> nm_of_comp n2
    | uu____2108 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let is_monadic_comp c =
  let uu____2120 = nm_of_comp c.FStar_Syntax_Syntax.n  in
  match uu____2120 with | M uu____2121 -> true | N uu____2122 -> false 
exception Not_found 
let uu___is_Not_found : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2126 -> false
  
let double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ0  ->
    let star_once typ01 =
      let uu____2134 =
        let uu____2135 =
          let uu____2136 = FStar_Syntax_Syntax.new_bv None typ01  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2136  in
        [uu____2135]  in
      let uu____2137 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____2134 uu____2137  in
    let uu____2138 = FStar_All.pipe_right typ0 star_once  in
    FStar_All.pipe_left star_once uu____2138
  
let rec mk_star_to_type :
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
          (let uu____2169 =
             let uu____2177 =
               let uu____2181 =
                 let uu____2184 =
                   let uu____2185 = star_type' env a  in
                   FStar_Syntax_Syntax.null_bv uu____2185  in
                 let uu____2186 = FStar_Syntax_Syntax.as_implicit false  in
                 (uu____2184, uu____2186)  in
               [uu____2181]  in
             let uu____2191 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
             (uu____2177, uu____2191)  in
           FStar_Syntax_Syntax.Tm_arrow uu____2169)

and star_type' :
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let mk1 x = (FStar_Syntax_Syntax.mk x) None t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type1 = mk_star_to_type mk1  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2224) ->
          let binders1 =
            FStar_List.map
              (fun uu____2243  ->
                 match uu____2243 with
                 | (bv,aqual) ->
                     let uu____2250 =
                       let uu___98_2251 = bv  in
                       let uu____2252 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___98_2251.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___98_2251.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2252
                       }  in
                     (uu____2250, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2255,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2257);
                             FStar_Syntax_Syntax.tk = uu____2258;
                             FStar_Syntax_Syntax.pos = uu____2259;
                             FStar_Syntax_Syntax.vars = uu____2260;_})
               ->
               let uu____2277 =
                 let uu____2278 =
                   let uu____2286 =
                     let uu____2287 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____2287  in
                   (binders1, uu____2286)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____2278  in
               mk1 uu____2277
           | uu____2291 ->
               let uu____2292 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____2292 with
                | N hn ->
                    let uu____2294 =
                      let uu____2295 =
                        let uu____2303 =
                          let uu____2304 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____2304  in
                        (binders1, uu____2303)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____2295  in
                    mk1 uu____2294
                | M a ->
                    let uu____2309 =
                      let uu____2310 =
                        let uu____2318 =
                          let uu____2322 =
                            let uu____2326 =
                              let uu____2329 =
                                let uu____2330 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____2330  in
                              let uu____2331 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____2329, uu____2331)  in
                            [uu____2326]  in
                          FStar_List.append binders1 uu____2322  in
                        let uu____2338 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____2318, uu____2338)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____2310  in
                    mk1 uu____2309))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2389 = f x  in
                    FStar_Util.string_builder_append strb uu____2389);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2393 = f x1  in
                         FStar_Util.string_builder_append strb uu____2393))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____2395 = FStar_Syntax_Print.term_to_string t2  in
            let uu____2396 = string_of_set FStar_Syntax_Print.bv_to_string s
               in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2395 uu____2396
             in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2404 =
              let uu____2405 = FStar_Syntax_Subst.compress ty  in
              uu____2405.FStar_Syntax_Syntax.n  in
            match uu____2404 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2420 =
                  let uu____2421 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____2421  in
                if uu____2420
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2435 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____2435 s  in
                       let uu____2437 =
                         let uu____2438 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____2438  in
                       if uu____2437
                       then (debug1 ty1 sinter; Prims.raise Not_found)
                       else ()  in
                     let uu____2441 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____2441 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2452  ->
                                  match uu____2452 with
                                  | (bv,uu____2458) ->
                                      (non_dependent_or_raise s
                                         bv.FStar_Syntax_Syntax.sort;
                                       FStar_Util.set_add bv s))
                             FStar_Syntax_Syntax.no_names binders1
                            in
                         let ct = FStar_TypeChecker_Env.result_typ env.env c1
                            in
                         (non_dependent_or_raise s ct;
                          (let k = n1 - (FStar_List.length binders1)  in
                           if k > (Prims.parse_int "0")
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found  -> false)
            | uu____2469 ->
                ((let uu____2471 = FStar_Syntax_Print.term_to_string ty  in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2471);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____2476 =
              let uu____2477 = FStar_Syntax_Subst.compress head2  in
              uu____2477.FStar_Syntax_Syntax.n  in
            match uu____2476 with
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
                  (let uu____2481 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____2481)
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
                      FStar_Syntax_Syntax.Delta_constant] env.env t1
                   in
                (match res.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_app uu____2494 -> true
                 | uu____2504 ->
                     ((let uu____2506 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2506);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
                true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2510) ->
                is_valid_application t2
            | uu____2515 -> false  in
          let uu____2516 = is_valid_application head1  in
          if uu____2516
          then
            let uu____2517 =
              let uu____2518 =
                let uu____2528 =
                  FStar_List.map
                    (fun uu____2538  ->
                       match uu____2538 with
                       | (t2,qual) ->
                           let uu____2551 = star_type' env t2  in
                           (uu____2551, qual)) args
                   in
                (head1, uu____2528)  in
              FStar_Syntax_Syntax.Tm_app uu____2518  in
            mk1 uu____2517
          else
            (let uu____2558 =
               let uu____2559 =
                 let uu____2560 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2560
                  in
               FStar_Errors.Err uu____2559  in
             Prims.raise uu____2558)
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_name _
         |FStar_Syntax_Syntax.Tm_type _|FStar_Syntax_Syntax.Tm_fvar _ -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2590 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____2590 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___101_2596 = env  in
                 let uu____2597 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____2597;
                   subst = (uu___101_2596.subst);
                   tc_const = (uu___101_2596.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 = [FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), x1)]
             in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 = [FStar_Syntax_Syntax.NM (x1, (Prims.parse_int "0"))]
             in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___102_2614 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___102_2614.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___102_2614.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2621 =
            let uu____2622 =
              let uu____2627 = star_type' env t2  in (uu____2627, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____2622  in
          mk1 uu____2621
      | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t2,something) ->
          let uu____2649 =
            let uu____2650 =
              let uu____2663 = star_type' env e  in
              let uu____2664 =
                let uu____2669 = star_type' env t2  in
                FStar_Util.Inl uu____2669  in
              (uu____2663, uu____2664, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2650  in
          mk1 uu____2649
      | FStar_Syntax_Syntax.Tm_ascribed uu____2677 ->
          let uu____2690 =
            let uu____2691 =
              let uu____2692 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2692
               in
            FStar_Errors.Err uu____2691  in
          Prims.raise uu____2690
      | FStar_Syntax_Syntax.Tm_refine uu____2693 ->
          let uu____2698 =
            let uu____2699 =
              let uu____2700 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2700
               in
            FStar_Errors.Err uu____2699  in
          Prims.raise uu____2698
      | FStar_Syntax_Syntax.Tm_uinst uu____2701 ->
          let uu____2706 =
            let uu____2707 =
              let uu____2708 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2708
               in
            FStar_Errors.Err uu____2707  in
          Prims.raise uu____2706
      | FStar_Syntax_Syntax.Tm_constant uu____2709 ->
          let uu____2710 =
            let uu____2711 =
              let uu____2712 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2712
               in
            FStar_Errors.Err uu____2711  in
          Prims.raise uu____2710
      | FStar_Syntax_Syntax.Tm_match uu____2713 ->
          let uu____2729 =
            let uu____2730 =
              let uu____2731 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2731
               in
            FStar_Errors.Err uu____2730  in
          Prims.raise uu____2729
      | FStar_Syntax_Syntax.Tm_let uu____2732 ->
          let uu____2740 =
            let uu____2741 =
              let uu____2742 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2742
               in
            FStar_Errors.Err uu____2741  in
          Prims.raise uu____2740
      | FStar_Syntax_Syntax.Tm_uvar uu____2743 ->
          let uu____2752 =
            let uu____2753 =
              let uu____2754 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2754
               in
            FStar_Errors.Err uu____2753  in
          Prims.raise uu____2752
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2755 =
            let uu____2756 =
              let uu____2757 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2757
               in
            FStar_Errors.Err uu____2756  in
          Prims.raise uu____2755
      | FStar_Syntax_Syntax.Tm_delayed uu____2758 -> failwith "impossible"

let is_monadic uu___87_2791 =
  match uu___87_2791 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
    { FStar_Syntax_Syntax.lcomp_name = _;
      FStar_Syntax_Syntax.lcomp_univs = _;
      FStar_Syntax_Syntax.lcomp_indices = _;
      FStar_Syntax_Syntax.lcomp_res_typ = _;
      FStar_Syntax_Syntax.lcomp_cflags = flags;
      FStar_Syntax_Syntax.lcomp_as_comp = _;_})|Some (FStar_Util.Inr
    (_,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___86_2830  ->
              match uu___86_2830 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____2831 -> false))
  
let rec is_C : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2835 =
      let uu____2836 = FStar_Syntax_Subst.compress t  in
      uu____2836.FStar_Syntax_Syntax.n  in
    match uu____2835 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2856 =
            let uu____2857 = FStar_List.hd args  in Prims.fst uu____2857  in
          is_C uu____2856  in
        if r
        then
          ((let uu____2869 =
              let uu____2870 =
                FStar_List.for_all
                  (fun uu____2873  ->
                     match uu____2873 with | (h,uu____2877) -> is_C h) args
                 in
              Prims.op_Negation uu____2870  in
            if uu____2869 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2881 =
              let uu____2882 =
                FStar_List.for_all
                  (fun uu____2885  ->
                     match uu____2885 with
                     | (h,uu____2889) ->
                         let uu____2890 = is_C h  in
                         Prims.op_Negation uu____2890) args
                 in
              Prims.op_Negation uu____2882  in
            if uu____2881 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2904 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____2904 with
         | M t1 ->
             ((let uu____2907 = is_C t1  in
               if uu____2907 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,_)
      |FStar_Syntax_Syntax.Tm_uinst (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
       (t1,_,_) -> is_C t1
    | uu____2934 -> false
  
let mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x = (FStar_Syntax_Syntax.mk x) None e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk1 env t  in
        let p = FStar_Syntax_Syntax.gen_bv "p'" None p_type  in
        let body =
          let uu____2965 =
            let uu____2966 =
              let uu____2976 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____2977 =
                let uu____2981 =
                  let uu____2984 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____2984)  in
                [uu____2981]  in
              (uu____2976, uu____2977)  in
            FStar_Syntax_Syntax.Tm_app uu____2966  in
          mk1 uu____2965  in
        let uu____2992 =
          let uu____2996 = FStar_Syntax_Syntax.mk_binder p  in [uu____2996]
           in
        FStar_Syntax_Util.abs uu____2992 body None
  
let is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___88_3004  ->
    match uu___88_3004 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3005 -> false
  
let rec check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos
           in
        let return_if uu____3147 =
          match uu____3147 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3168 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3169 =
                       let uu____3170 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____3170  in
                     Prims.op_Negation uu____3169)
                   in
                if uu____3168
                then
                  let uu____3171 =
                    let uu____3172 =
                      let uu____3173 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____3174 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____3175 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3173 uu____3174 uu____3175
                       in
                    FStar_Errors.Err uu____3172  in
                  Prims.raise uu____3171
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2)|(M t1,M t2) ->
                   (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3186 = mk_return env t1 s_e  in
                     ((M t1), uu____3186, u_e)))
               | (M t1,N t2) ->
                   let uu____3189 =
                     let uu____3190 =
                       let uu____3191 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____3192 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____3193 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3191 uu____3192 uu____3193
                        in
                     FStar_Errors.Err uu____3190  in
                   Prims.raise uu____3189)
           in
        let ensure_m env1 e2 =
          let strip_m uu___89_3219 =
            match uu___89_3219 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3229 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____3240 =
                let uu____3241 =
                  let uu____3244 =
                    let uu____3245 = FStar_Syntax_Print.term_to_string t  in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3245
                     in
                  (uu____3244, (e2.FStar_Syntax_Syntax.pos))  in
                FStar_Errors.Error uu____3241  in
              Prims.raise uu____3240
          | M uu____3249 ->
              let uu____3250 = check env1 e2 context_nm  in
              strip_m uu____3250
           in
        let uu____3254 =
          let uu____3255 = FStar_Syntax_Subst.compress e  in
          uu____3255.FStar_Syntax_Syntax.n  in
        match uu____3254 with
        | FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_name _
           |FStar_Syntax_Syntax.Tm_fvar _
            |FStar_Syntax_Syntax.Tm_abs _
             |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_app _
            -> let uu____3267 = infer env e  in return_if uu____3267
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
        | FStar_Syntax_Syntax.Tm_let uu____3337 ->
            let uu____3345 =
              let uu____3346 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3346  in
            failwith uu____3345
        | FStar_Syntax_Syntax.Tm_type uu____3350 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3354 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3365 ->
            let uu____3370 =
              let uu____3371 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3371  in
            failwith uu____3370
        | FStar_Syntax_Syntax.Tm_uvar uu____3375 ->
            let uu____3384 =
              let uu____3385 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3385  in
            failwith uu____3384
        | FStar_Syntax_Syntax.Tm_delayed uu____3389 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3413 =
              let uu____3414 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3414  in
            failwith uu____3413

and infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mk1 x = FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos  in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env
         in
      let uu____3436 =
        let uu____3437 = FStar_Syntax_Subst.compress e  in
        uu____3437.FStar_Syntax_Syntax.n  in
      match uu____3436 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let env1 =
            let uu___103_3477 = env  in
            let uu____3478 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____3478;
              subst = (uu___103_3477.subst);
              tc_const = (uu___103_3477.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____3487  ->
                 match uu____3487 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___104_3495 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___104_3495.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___104_3495.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____3496 =
            FStar_List.fold_left
              (fun uu____3505  ->
                 fun uu____3506  ->
                   match (uu____3505, uu____3506) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____3534 = is_C c  in
                       if uu____3534
                       then
                         let xw =
                           let uu____3539 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "^w") None uu____3539
                            in
                         let x =
                           let uu___105_3541 = bv  in
                           let uu____3542 =
                             let uu____3545 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____3545  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___105_3541.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___105_3541.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3542
                           }  in
                         let env3 =
                           let uu___106_3547 = env2  in
                           let uu____3548 =
                             let uu____3550 =
                               let uu____3551 =
                                 let uu____3556 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____3556)  in
                               FStar_Syntax_Syntax.NT uu____3551  in
                             uu____3550 :: (env2.subst)  in
                           {
                             env = (uu___106_3547.env);
                             subst = uu____3548;
                             tc_const = (uu___106_3547.tc_const)
                           }  in
                         let uu____3557 =
                           let uu____3559 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____3560 =
                             let uu____3562 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____3562 :: acc  in
                           uu____3559 :: uu____3560  in
                         (env3, uu____3557)
                       else
                         (let x =
                            let uu___107_3566 = bv  in
                            let uu____3567 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___107_3566.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___107_3566.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3567
                            }  in
                          let uu____3570 =
                            let uu____3572 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____3572 :: acc  in
                          (env2, uu____3570))) (env1, []) binders1
             in
          (match uu____3496 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____3584 =
                 let check_what =
                   let uu____3596 = is_monadic what  in
                   if uu____3596 then check_m else check_n  in
                 let uu____3605 = check_what env2 body1  in
                 match uu____3605 with
                 | (t,s_body,u_body) ->
                     let uu____3615 =
                       let uu____3616 =
                         let uu____3617 = is_monadic what  in
                         if uu____3617 then M t else N t  in
                       comp_of_nm uu____3616  in
                     (uu____3615, s_body, u_body)
                  in
               (match uu____3584 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3658 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.lcomp_cflags
                              (FStar_Util.for_some
                                 (fun uu___90_3660  ->
                                    match uu___90_3660 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3661 -> false))
                             in
                          if uu____3658
                          then
                            let double_starred_comp =
                              let uu____3669 =
                                let uu____3670 =
                                  let uu____3671 =
                                    lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                                     in
                                  FStar_TypeChecker_Env.result_typ env2.env
                                    uu____3671
                                   in
                                FStar_All.pipe_left double_star uu____3670
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____3669  in
                            let flags =
                              FStar_List.filter
                                (fun uu___91_3674  ->
                                   match uu___91_3674 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3675 -> true)
                                lc.FStar_Syntax_Syntax.lcomp_cflags
                               in
                            let uu____3676 =
                              let uu____3682 =
                                let uu____3683 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags
                                   in
                                FStar_TypeChecker_Env.lcomp_of_comp env2.env
                                  uu____3683
                                 in
                              FStar_Util.Inl uu____3682  in
                            Some uu____3676
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___108_3701 = lc  in
                                   {
                                     FStar_Syntax_Syntax.lcomp_name =
                                       (uu___108_3701.FStar_Syntax_Syntax.lcomp_name);
                                     FStar_Syntax_Syntax.lcomp_univs =
                                       (uu___108_3701.FStar_Syntax_Syntax.lcomp_univs);
                                     FStar_Syntax_Syntax.lcomp_indices =
                                       (uu___108_3701.FStar_Syntax_Syntax.lcomp_indices);
                                     FStar_Syntax_Syntax.lcomp_res_typ =
                                       (uu___108_3701.FStar_Syntax_Syntax.lcomp_res_typ);
                                     FStar_Syntax_Syntax.lcomp_cflags =
                                       (uu___108_3701.FStar_Syntax_Syntax.lcomp_cflags);
                                     FStar_Syntax_Syntax.lcomp_as_comp =
                                       (fun uu____3702  ->
                                          let c =
                                            lc.FStar_Syntax_Syntax.lcomp_as_comp
                                              ()
                                             in
                                          let nct =
                                            FStar_TypeChecker_Env.comp_as_normal_comp_typ
                                              env2.env c
                                             in
                                          let result_typ1 =
                                            star_type' env2
                                              (Prims.fst
                                                 nct.FStar_TypeChecker_Env.nct_result)
                                             in
                                          let nct' =
                                            let uu___109_3711 = nct  in
                                            let uu____3712 =
                                              FStar_Syntax_Syntax.as_arg
                                                result_typ1
                                               in
                                            {
                                              FStar_TypeChecker_Env.nct_name
                                                =
                                                (uu___109_3711.FStar_TypeChecker_Env.nct_name);
                                              FStar_TypeChecker_Env.nct_univs
                                                =
                                                (uu___109_3711.FStar_TypeChecker_Env.nct_univs);
                                              FStar_TypeChecker_Env.nct_indices
                                                =
                                                (uu___109_3711.FStar_TypeChecker_Env.nct_indices);
                                              FStar_TypeChecker_Env.nct_result
                                                = uu____3712;
                                              FStar_TypeChecker_Env.nct_wp =
                                                (uu___109_3711.FStar_TypeChecker_Env.nct_wp);
                                              FStar_TypeChecker_Env.nct_flags
                                                =
                                                (uu___109_3711.FStar_TypeChecker_Env.nct_flags)
                                            }  in
                                          FStar_TypeChecker_Env.normal_comp_typ_as_comp
                                            env2.env nct')
                                   })))
                      | Some (FStar_Util.Inr (lid,flags)) ->
                          let uu____3725 =
                            let uu____3731 =
                              let uu____3735 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___92_3737  ->
                                        match uu___92_3737 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____3738 -> false))
                                 in
                              if uu____3735
                              then
                                let uu____3742 =
                                  FStar_List.filter
                                    (fun uu___93_3744  ->
                                       match uu___93_3744 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____3745 -> true) flags
                                   in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____3742)
                              else (lid, flags)  in
                            FStar_Util.Inr uu____3731  in
                          Some uu____3725
                       in
                    let uu____3757 =
                      let comp1 =
                        let uu____3769 =
                          FStar_TypeChecker_Env.result_typ env2.env comp  in
                        let uu____3770 = is_monadic what  in
                        let uu____3771 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 uu____3769 uu____3770 uu____3771  in
                      let uu____3772 =
                        FStar_Syntax_Util.ascribe u_body
                          (FStar_Util.Inr comp1)
                         in
                      let uu____3777 =
                        let uu____3784 =
                          let uu____3790 =
                            FStar_TypeChecker_Env.lcomp_of_comp env2.env
                              comp1
                             in
                          FStar_Util.Inl uu____3790  in
                        Some uu____3784  in
                      (uu____3772, uu____3777)  in
                    (match uu____3757 with
                     | (u_body1,u_what) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           mk1
                             (FStar_Syntax_Syntax.Tm_abs
                                (s_binders1, s_body1, s_what))
                            in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           mk1
                             (FStar_Syntax_Syntax.Tm_abs
                                (u_binders2, u_body2, u_what))
                            in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.ty = uu____3855;
                FStar_Syntax_Syntax.p = uu____3856;_};
            FStar_Syntax_Syntax.fv_delta = uu____3857;
            FStar_Syntax_Syntax.fv_qual = uu____3858;_}
          ->
          let uu____3864 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
          (match uu____3864 with
           | (uu____3870,t) ->
               let txt = FStar_Ident.text_of_lid lid  in
               let uu____3873 =
                 let uu____3874 = normalize1 t  in N uu____3874  in
               (uu____3873, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3891 = check_n env head1  in
          (match uu____3891 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____3905 =
                   let uu____3906 = FStar_Syntax_Subst.compress t  in
                   uu____3906.FStar_Syntax_Syntax.n  in
                 match uu____3905 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____3909 -> true
                 | uu____3917 -> false  in
               let rec flatten1 t =
                 let uu____3929 =
                   let uu____3930 = FStar_Syntax_Subst.compress t  in
                   uu____3930.FStar_Syntax_Syntax.n  in
                 match uu____3929 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____3942);
                                FStar_Syntax_Syntax.tk = uu____3943;
                                FStar_Syntax_Syntax.pos = uu____3944;
                                FStar_Syntax_Syntax.vars = uu____3945;_})
                     when is_arrow t1 ->
                     let uu____3962 = flatten1 t1  in
                     (match uu____3962 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4014,uu____4015)
                     -> flatten1 e1
                 | uu____4034 ->
                     let uu____4035 =
                       let uu____4036 =
                         let uu____4037 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4037
                          in
                       FStar_Errors.Err uu____4036  in
                     Prims.raise uu____4035
                  in
               let uu____4045 = flatten1 t_head  in
               (match uu____4045 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4090 =
                          let uu____4091 =
                            let uu____4092 = FStar_Util.string_of_int n1  in
                            let uu____4096 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____4102 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4092 uu____4096 uu____4102
                             in
                          FStar_Errors.Err uu____4091  in
                        Prims.raise uu____4090)
                     else ();
                     (let uu____4107 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____4107 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4134 args1 =
                            match uu____4134 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4177 =
                                       let uu____4178 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____4178.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____4177
                                 | (binders3,[]) ->
                                     let uu____4197 =
                                       let uu____4198 =
                                         let uu____4201 =
                                           let uu____4202 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4202
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____4201
                                          in
                                       uu____4198.FStar_Syntax_Syntax.n  in
                                     (match uu____4197 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4218 =
                                            let uu____4219 =
                                              let uu____4220 =
                                                let uu____4228 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____4228)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4220
                                               in
                                            mk1 uu____4219  in
                                          N uu____4218
                                      | uu____4232 -> failwith "wat?")
                                 | ([],uu____4233::uu____4234) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4259)::binders3,(arg,uu____4262)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____4296 = FStar_List.splitAt n' binders1  in
                          (match uu____4296 with
                           | (binders2,uu____4313) ->
                               let uu____4326 =
                                 let uu____4336 =
                                   FStar_List.map2
                                     (fun uu____4356  ->
                                        fun uu____4357  ->
                                          match (uu____4356, uu____4357) with
                                          | ((bv,uu____4374),(arg,q)) ->
                                              let uu____4381 =
                                                let uu____4382 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____4382.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____4381 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4392 ->
                                                   let arg1 = (arg, q)  in
                                                   (arg1, [arg1])
                                               | uu____4405 ->
                                                   let uu____4406 =
                                                     check_n env arg  in
                                                   (match uu____4406 with
                                                    | (uu____4417,s_arg,u_arg)
                                                        ->
                                                        let uu____4420 =
                                                          let uu____4424 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____4424
                                                          then
                                                            let uu____4428 =
                                                              let uu____4431
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____4431, q)
                                                               in
                                                            [uu____4428;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____4420))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____4336  in
                               (match uu____4326 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____4478 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____4484 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____4478, uu____4484)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,_)
        |FStar_Syntax_Syntax.Tm_meta (e1,_)|FStar_Syntax_Syntax.Tm_ascribed
         (e1,_,_) -> infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4557 = let uu____4558 = env.tc_const c  in N uu____4558
             in
          (uu____4557, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4559 ->
          let uu____4567 =
            let uu____4568 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4568  in
          failwith uu____4567
      | FStar_Syntax_Syntax.Tm_type uu____4572 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4576 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4587 ->
          let uu____4592 =
            let uu____4593 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4593  in
          failwith uu____4592
      | FStar_Syntax_Syntax.Tm_uvar uu____4597 ->
          let uu____4606 =
            let uu____4607 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4607  in
          failwith uu____4606
      | FStar_Syntax_Syntax.Tm_delayed uu____4611 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4635 =
            let uu____4636 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4636  in
          failwith uu____4635

and mk_match :
  env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.withinfo_t *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option *
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos  in
          let uu____4674 = check_n env e0  in
          match uu____4674 with
          | (uu____4681,s_e0,u_e0) ->
              let uu____4684 =
                let uu____4702 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4735 = FStar_Syntax_Subst.open_branch b  in
                       match uu____4735 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___110_4767 = env  in
                             let uu____4768 =
                               let uu____4769 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4769
                                in
                             {
                               env = uu____4768;
                               subst = (uu___110_4767.subst);
                               tc_const = (uu___110_4767.tc_const)
                             }  in
                           let uu____4771 = f env1 body  in
                           (match uu____4771 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4820 ->
                           Prims.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____4702  in
              (match uu____4684 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____4885 = FStar_List.hd nms  in
                     match uu____4885 with | M t1|N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___94_4888  ->
                          match uu___94_4888 with
                          | M uu____4889 -> true
                          | uu____4890 -> false) nms
                      in
                   let uu____4891 =
                     let uu____4914 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____4966  ->
                              match uu____4966 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false )|(M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5062 =
                                         check env original_body (M t2)  in
                                       (match uu____5062 with
                                        | (uu____5085,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5114,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____4914  in
                   (match uu____4891 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5233  ->
                                 match uu____5233 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5274 =
                                         let uu____5275 =
                                           let uu____5285 =
                                             let uu____5289 =
                                               let uu____5292 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____5293 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____5292, uu____5293)  in
                                             [uu____5289]  in
                                           (s_body, uu____5285)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5275
                                          in
                                       mk1 uu____5274  in
                                     (pat, guard, s_body1)) s_branches
                             in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1
                             in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches
                             in
                          let s_e =
                            let uu____5315 =
                              let uu____5319 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____5319]  in
                            let uu____5320 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____5315 uu____5320 None
                             in
                          let t1_star =
                            let uu____5328 =
                              let uu____5329 =
                                let uu____5330 =
                                  FStar_Syntax_Syntax.new_bv None p_type  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5330
                                 in
                              [uu____5329]  in
                            let uu____5331 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____5328 uu____5331  in
                          let uu____5332 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, (FStar_Util.Inl t1_star), None))
                             in
                          let uu____5342 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____5332, uu____5342)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches
                              in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches
                              in
                           let t1_star = t1  in
                           let uu____5356 =
                             let uu____5359 =
                               let uu____5360 =
                                 let uu____5373 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____5373, (FStar_Util.Inl t1_star), None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5360  in
                             mk1 uu____5359  in
                           let uu____5386 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____5356, uu____5386))))

and mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
                 FStar_Syntax_Syntax.term))
            -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x None e2.FStar_Syntax_Syntax.pos  in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____5429 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____5429]  in
            let uu____5430 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____5430 with
            | (x_binders1,e21) ->
                let uu____5438 = infer env e1  in
                (match uu____5438 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5449 = is_C t1  in
                       if uu____5449
                       then
                         let uu___111_5450 = binding  in
                         let uu____5451 =
                           let uu____5454 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____5454  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___111_5450.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___111_5450.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5451;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___111_5450.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___111_5450.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding  in
                     let env1 =
                       let uu___112_5457 = env  in
                       let uu____5458 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___113_5459 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___113_5459.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___113_5459.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____5458;
                         subst = (uu___112_5457.subst);
                         tc_const = (uu___112_5457.tc_const)
                       }  in
                     let uu____5460 = proceed env1 e21  in
                     (match uu____5460 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___114_5471 = binding  in
                            let uu____5472 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___114_5471.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___114_5471.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5472;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___114_5471.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___114_5471.FStar_Syntax_Syntax.lbdef)
                            }  in
                          let uu____5475 =
                            let uu____5478 =
                              let uu____5479 =
                                let uu____5487 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___115_5492 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___115_5492.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___115_5492.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___115_5492.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___115_5492.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5487)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5479  in
                            mk1 uu____5478  in
                          let uu____5493 =
                            let uu____5496 =
                              let uu____5497 =
                                let uu____5505 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___116_5510 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___116_5510.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___116_5510.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___116_5510.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___116_5510.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5505)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5497  in
                            mk1 uu____5496  in
                          (nm_rec, uu____5475, uu____5493))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___117_5519 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___117_5519.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___117_5519.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___117_5519.FStar_Syntax_Syntax.lbdef)
                       }  in
                     let env1 =
                       let uu___118_5521 = env  in
                       let uu____5522 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___119_5523 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___119_5523.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___119_5523.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____5522;
                         subst = (uu___118_5521.subst);
                         tc_const = (uu___118_5521.tc_const)
                       }  in
                     let uu____5524 = ensure_m env1 e21  in
                     (match uu____5524 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_e21 =
                            let uu____5541 =
                              let uu____5542 =
                                let uu____5552 =
                                  let uu____5556 =
                                    let uu____5559 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____5560 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____5559, uu____5560)  in
                                  [uu____5556]  in
                                (s_e2, uu____5552)  in
                              FStar_Syntax_Syntax.Tm_app uu____5542  in
                            mk1 uu____5541  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21 None  in
                          let body =
                            let uu____5577 =
                              let uu____5578 =
                                let uu____5588 =
                                  let uu____5592 =
                                    let uu____5595 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____5595)  in
                                  [uu____5592]  in
                                (s_e1, uu____5588)  in
                              FStar_Syntax_Syntax.Tm_app uu____5578  in
                            mk1 uu____5577  in
                          let uu____5603 =
                            let uu____5604 =
                              let uu____5608 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____5608]  in
                            FStar_Syntax_Util.abs uu____5604 body None  in
                          let uu____5614 =
                            let uu____5617 =
                              let uu____5618 =
                                let uu____5626 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___120_5631 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___120_5631.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___120_5631.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___120_5631.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___120_5631.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5626)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5618  in
                            mk1 uu____5617  in
                          ((M t2), uu____5603, uu____5614)))

and check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5640 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos
           in
        N uu____5640  in
      let uu____5645 = check env e mn  in
      match uu____5645 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5655 -> failwith "[check_n]: impossible"

and check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5668 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos
           in
        M uu____5668  in
      let uu____5673 = check env e mn  in
      match uu____5673 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5683 -> failwith "[check_m]: impossible"

and comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp =
  fun t  ->
    let uu____5694 =
      let uu____5695 =
        let uu____5701 = FStar_Syntax_Syntax.as_arg t  in [uu____5701]  in
      {
        FStar_Syntax_Syntax.comp_typ_name = FStar_Syntax_Const.monadic_lid;
        FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
        FStar_Syntax_Syntax.effect_args = uu____5695;
        FStar_Syntax_Syntax.flags =
          [FStar_Syntax_Syntax.CPS; FStar_Syntax_Syntax.TOTAL]
      }  in
    FStar_Syntax_Syntax.mk_Comp uu____5694

and type_of_comp : env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.typ
  = fun env  -> fun t  -> FStar_TypeChecker_Env.result_typ env.env t

and trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____5708 =
           let uu____5709 = is_C c  in Prims.op_Negation uu____5709  in
         if uu____5708 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos
            in
         let uu____5721 =
           let uu____5722 = FStar_Syntax_Subst.compress c  in
           uu____5722.FStar_Syntax_Syntax.n  in
         match uu____5721 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5741 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____5741 with
              | (wp_head,wp_args) ->
                  ((let uu____5768 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____5781 =
                           let uu____5782 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____5782
                            in
                         Prims.op_Negation uu____5781)
                       in
                    if uu____5768 then failwith "mismatch" else ());
                   (let uu____5791 =
                      let uu____5792 =
                        let uu____5802 =
                          FStar_List.map2
                            (fun uu____5812  ->
                               fun uu____5813  ->
                                 match (uu____5812, uu____5813) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____5836 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____5836
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____5839 = print_implicit q
                                            in
                                         let uu____5840 = print_implicit q'
                                            in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____5839 uu____5840)
                                      else ();
                                      (let uu____5842 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____5842, q)))) args wp_args
                           in
                        (head1, uu____5802)  in
                      FStar_Syntax_Syntax.Tm_app uu____5792  in
                    mk1 uu____5791)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____5864 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____5864 with
              | (binders_orig,comp1) ->
                  let uu____5869 =
                    let uu____5877 =
                      FStar_List.map
                        (fun uu____5891  ->
                           match uu____5891 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____5904 = is_C h  in
                               if uu____5904
                               then
                                 let w' =
                                   let uu____5911 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "-w'") None uu____5911
                                    in
                                 let uu____5912 =
                                   let uu____5916 =
                                     let uu____5920 =
                                       let uu____5923 =
                                         let uu____5924 =
                                           let uu____5925 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____5925  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____5924
                                          in
                                       (uu____5923, q)  in
                                     [uu____5920]  in
                                   (w', q) :: uu____5916  in
                                 (w', uu____5912)
                               else
                                 (let x =
                                    let uu____5937 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "-x") None uu____5937
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____5877  in
                  (match uu____5869 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____5967 =
                           let uu____5969 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____5969
                            in
                         FStar_Syntax_Subst.subst_comp uu____5967 comp1  in
                       let app =
                         let uu____5973 =
                           let uu____5974 =
                             let uu____5984 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____5991 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____5992 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____5991, uu____5992)) bvs
                                in
                             (wp, uu____5984)  in
                           FStar_Syntax_Syntax.Tm_app uu____5974  in
                         mk1 uu____5973  in
                       let comp3 =
                         let uu____5997 = type_of_comp env comp2  in
                         let uu____5998 = is_monadic_comp comp2  in
                         trans_G env uu____5997 uu____5998 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6000,uu____6001) ->
             trans_F_ env e wp
         | uu____6020 -> failwith "impossible trans_F_")

and trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          let mk1 x = FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos
             in
          if is_monadic1
          then
            let uu____6035 =
              let uu____6036 =
                let uu____6042 =
                  let uu____6043 = star_type' env h  in
                  FStar_Syntax_Syntax.as_arg uu____6043  in
                let uu____6044 =
                  let uu____6046 = FStar_Syntax_Syntax.as_arg wp  in
                  [uu____6046]  in
                uu____6042 :: uu____6044  in
              {
                FStar_Syntax_Syntax.comp_typ_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_args = uu____6036;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____6035
          else
            (let uu____6048 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____6048)

let n :
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
  
let star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  -> let uu____6059 = n env.env t  in star_type' env uu____6059
  
let star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6071 = n env.env t  in check_n env uu____6071
  
let trans_F :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6081 = n env.env c  in
        let uu____6082 = n env.env wp  in trans_F_ env uu____6081 uu____6082
  