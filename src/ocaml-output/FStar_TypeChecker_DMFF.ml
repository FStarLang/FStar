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
              let uu___97_64 = a  in
              let uu____65 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___97_64.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___97_64.FStar_Syntax_Syntax.index);
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
                      let uu____285 = f (FStar_Syntax_Syntax.bv_to_name t)
                         in
                      FStar_Syntax_Util.arrow gamma uu____285  in
                    let uu____288 =
                      let uu____292 =
                        let uu____296 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____297 =
                          let uu____299 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____299]  in
                        uu____296 :: uu____297  in
                      FStar_List.append binders uu____292  in
                    FStar_Syntax_Util.abs uu____288 body None  in
                  let uu____307 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____308 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____307, uu____308)  in
                match uu____265 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
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
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____370 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____369, uu____370)) binders
                               in
                            let uu____371 =
                              let uu____375 =
                                let uu____378 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____379 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____378, uu____379)  in
                              let uu____380 =
                                let uu____384 =
                                  let uu____387 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____387)  in
                                [uu____384]  in
                              uu____375 :: uu____380  in
                            FStar_List.append uu____354 uu____371  in
                          (fv, uu____350)  in
                        FStar_Syntax_Syntax.Tm_app uu____340  in
                      mk1 uu____339  in
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
                      let uu____433 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____433  in
                    let ret1 =
                      let uu____441 =
                        let uu____447 =
                          let uu____448 =
                            let uu____451 =
                              let uu____452 =
                                FStar_Syntax_Syntax.bv_to_name t  in
                              mk_ctx uu____452  in
                            FStar_Syntax_Syntax.mk_Total uu____451  in
                          FStar_Syntax_Util.lcomp_of_comp uu____448  in
                        FStar_Util.Inl uu____447  in
                      Some uu____441  in
                    let body =
                      let uu____462 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____462 ret1  in
                    let uu____463 =
                      let uu____467 = mk_all_implicit binders  in
                      let uu____471 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____467 uu____471  in
                    FStar_Syntax_Util.abs uu____463 body ret1  in
                  let c_pure1 =
                    let uu____486 = mk_lid "pure"  in
                    register env1 uu____486 c_pure  in
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
                      let uu____491 =
                        let uu____492 =
                          let uu____493 =
                            let uu____497 =
                              let uu____498 =
                                let uu____499 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv None uu____499  in
                              FStar_Syntax_Syntax.mk_binder uu____498  in
                            [uu____497]  in
                          let uu____500 =
                            let uu____503 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____503  in
                          FStar_Syntax_Util.arrow uu____493 uu____500  in
                        mk_gctx uu____492  in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____491  in
                    let r =
                      let uu____505 =
                        let uu____506 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____506  in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____505  in
                    let ret1 =
                      let uu____514 =
                        let uu____520 =
                          let uu____521 =
                            let uu____524 =
                              let uu____525 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              mk_gctx uu____525  in
                            FStar_Syntax_Syntax.mk_Total uu____524  in
                          FStar_Syntax_Util.lcomp_of_comp uu____521  in
                        FStar_Util.Inl uu____520  in
                      Some uu____514  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____540 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____543 =
                          let uu____549 =
                            let uu____551 =
                              let uu____552 =
                                let uu____553 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____553
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____552  in
                            [uu____551]  in
                          FStar_List.append gamma_as_args uu____549  in
                        FStar_Syntax_Util.mk_app uu____540 uu____543  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____556 =
                      let uu____560 = mk_all_implicit binders  in
                      let uu____564 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____560 uu____564  in
                    FStar_Syntax_Util.abs uu____556 outer_body ret1  in
                  let c_app1 =
                    let uu____583 = mk_lid "app"  in
                    register env1 uu____583 c_app  in
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
                      let uu____590 =
                        let uu____594 =
                          let uu____595 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____595  in
                        [uu____594]  in
                      let uu____596 =
                        let uu____599 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____599  in
                      FStar_Syntax_Util.arrow uu____590 uu____596  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a11 =
                      let uu____602 =
                        let uu____603 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____603  in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____602  in
                    let ret1 =
                      let uu____611 =
                        let uu____617 =
                          let uu____618 =
                            let uu____621 =
                              let uu____622 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              mk_gctx uu____622  in
                            FStar_Syntax_Syntax.mk_Total uu____621  in
                          FStar_Syntax_Util.lcomp_of_comp uu____618  in
                        FStar_Util.Inl uu____617  in
                      Some uu____611  in
                    let uu____631 =
                      let uu____635 = mk_all_implicit binders  in
                      let uu____639 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____635 uu____639  in
                    let uu____657 =
                      let uu____658 =
                        let uu____664 =
                          let uu____666 =
                            let uu____669 =
                              let uu____675 =
                                let uu____677 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____677]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____675
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____669  in
                          let uu____678 =
                            let uu____682 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____682]  in
                          uu____666 :: uu____678  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____664
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____658  in
                    FStar_Syntax_Util.abs uu____631 uu____657 ret1  in
                  let c_lift11 =
                    let uu____686 = mk_lid "lift1"  in
                    register env1 uu____686 c_lift1  in
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
                      let uu____694 =
                        let uu____698 =
                          let uu____699 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____699  in
                        let uu____700 =
                          let uu____702 =
                            let uu____703 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.null_binder uu____703  in
                          [uu____702]  in
                        uu____698 :: uu____700  in
                      let uu____704 =
                        let uu____707 = FStar_Syntax_Syntax.bv_to_name t3  in
                        FStar_Syntax_Syntax.mk_GTotal uu____707  in
                      FStar_Syntax_Util.arrow uu____694 uu____704  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a11 =
                      let uu____710 =
                        let uu____711 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____711  in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____710  in
                    let a2 =
                      let uu____713 =
                        let uu____714 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____714  in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____713  in
                    let ret1 =
                      let uu____722 =
                        let uu____728 =
                          let uu____729 =
                            let uu____732 =
                              let uu____733 =
                                FStar_Syntax_Syntax.bv_to_name t3  in
                              mk_gctx uu____733  in
                            FStar_Syntax_Syntax.mk_Total uu____732  in
                          FStar_Syntax_Util.lcomp_of_comp uu____729  in
                        FStar_Util.Inl uu____728  in
                      Some uu____722  in
                    let uu____742 =
                      let uu____746 = mk_all_implicit binders  in
                      let uu____750 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____746 uu____750  in
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
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____803]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____801
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____795
                                   in
                                let uu____804 =
                                  let uu____808 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____808]  in
                                uu____792 :: uu____804  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____790
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____784  in
                          let uu____811 =
                            let uu____815 = FStar_Syntax_Syntax.bv_to_name a2
                               in
                            [uu____815]  in
                          uu____781 :: uu____811  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____779
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____773  in
                    FStar_Syntax_Util.abs uu____742 uu____772 ret1  in
                  let c_lift21 =
                    let uu____819 = mk_lid "lift2"  in
                    register env1 uu____819 c_lift2  in
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
                      let uu____826 =
                        let uu____830 =
                          let uu____831 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____831  in
                        [uu____830]  in
                      let uu____832 =
                        let uu____835 =
                          let uu____836 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____836  in
                        FStar_Syntax_Syntax.mk_Total uu____835  in
                      FStar_Syntax_Util.arrow uu____826 uu____832  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let ret1 =
                      let uu____845 =
                        let uu____851 =
                          let uu____852 =
                            let uu____855 =
                              let uu____856 =
                                let uu____857 =
                                  let uu____861 =
                                    let uu____862 =
                                      FStar_Syntax_Syntax.bv_to_name t1  in
                                    FStar_Syntax_Syntax.null_binder uu____862
                                     in
                                  [uu____861]  in
                                let uu____863 =
                                  let uu____866 =
                                    FStar_Syntax_Syntax.bv_to_name t2  in
                                  FStar_Syntax_Syntax.mk_GTotal uu____866  in
                                FStar_Syntax_Util.arrow uu____857 uu____863
                                 in
                              mk_ctx uu____856  in
                            FStar_Syntax_Syntax.mk_Total uu____855  in
                          FStar_Syntax_Util.lcomp_of_comp uu____852  in
                        FStar_Util.Inl uu____851  in
                      Some uu____845  in
                    let e1 =
                      let uu____876 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____876  in
                    let body =
                      let uu____878 =
                        let uu____882 =
                          let uu____886 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____886]  in
                        FStar_List.append gamma uu____882  in
                      let uu____889 =
                        let uu____890 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____893 =
                          let uu____899 =
                            let uu____900 = FStar_Syntax_Syntax.bv_to_name e1
                               in
                            FStar_Syntax_Syntax.as_arg uu____900  in
                          let uu____901 = args_of_binders1 gamma  in
                          uu____899 :: uu____901  in
                        FStar_Syntax_Util.mk_app uu____890 uu____893  in
                      FStar_Syntax_Util.abs uu____878 uu____889 ret1  in
                    let uu____903 =
                      let uu____907 = mk_all_implicit binders  in
                      let uu____911 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____907 uu____911  in
                    FStar_Syntax_Util.abs uu____903 body ret1  in
                  let c_push1 =
                    let uu____928 = mk_lid "push"  in
                    register env1 uu____928 c_push  in
                  let ret_tot_wp_a =
                    let uu____936 =
                      let uu____942 =
                        let uu____943 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.lcomp_of_comp uu____943  in
                      FStar_Util.Inl uu____942  in
                    Some uu____936  in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____971 =
                        let uu____972 =
                          let uu____982 = args_of_binders1 binders  in
                          (c, uu____982)  in
                        FStar_Syntax_Syntax.Tm_app uu____972  in
                      mk1 uu____971
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____990 =
                        let uu____991 =
                          let uu____995 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____996 =
                            let uu____998 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____998]  in
                          uu____995 :: uu____996  in
                        let uu____999 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____991 uu____999  in
                      FStar_Syntax_Syntax.mk_Total uu____990  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype
                       in
                    let uu____1003 =
                      let uu____1007 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1007  in
                    let uu____1013 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None
                         in
                      let uu____1015 =
                        let uu____1018 =
                          let uu____1024 =
                            let uu____1026 =
                              let uu____1029 =
                                let uu____1035 =
                                  let uu____1036 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1036  in
                                [uu____1035]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1029  in
                            [uu____1026]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1024
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1018  in
                      FStar_Syntax_Util.ascribe uu____1015
                        ((FStar_Util.Inr result_comp), None)
                       in
                    FStar_Syntax_Util.abs uu____1003 uu____1013
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp)))
                     in
                  let wp_if_then_else1 =
                    let uu____1061 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1061 wp_if_then_else  in
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
                      let uu____1072 =
                        let uu____1078 =
                          let uu____1080 =
                            let uu____1083 =
                              let uu____1089 =
                                let uu____1091 =
                                  let uu____1094 =
                                    let uu____1100 =
                                      let uu____1101 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1101
                                       in
                                    [uu____1100]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1094
                                   in
                                [uu____1091]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1089
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1083  in
                          let uu____1106 =
                            let uu____1110 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1110]  in
                          uu____1080 :: uu____1106  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1078
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1072  in
                    let uu____1113 =
                      let uu____1117 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1117  in
                    FStar_Syntax_Util.abs uu____1113 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1124 = mk_lid "wp_assert"  in
                    register env1 uu____1124 wp_assert  in
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
                      let uu____1135 =
                        let uu____1141 =
                          let uu____1143 =
                            let uu____1146 =
                              let uu____1152 =
                                let uu____1154 =
                                  let uu____1157 =
                                    let uu____1163 =
                                      let uu____1164 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1164
                                       in
                                    [uu____1163]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1157
                                   in
                                [uu____1154]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1152
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1146  in
                          let uu____1169 =
                            let uu____1173 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1173]  in
                          uu____1143 :: uu____1169  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1141
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1135  in
                    let uu____1176 =
                      let uu____1180 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1180  in
                    FStar_Syntax_Util.abs uu____1176 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1187 = mk_lid "wp_assume"  in
                    register env1 uu____1187 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1196 =
                        let uu____1200 =
                          let uu____1201 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1201  in
                        [uu____1200]  in
                      let uu____1202 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1196 uu____1202  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let body =
                      let uu____1209 =
                        let uu____1215 =
                          let uu____1217 =
                            let uu____1220 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1220  in
                          let uu____1226 =
                            let uu____1230 =
                              let uu____1233 =
                                let uu____1239 =
                                  let uu____1241 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1241]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1239
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1233  in
                            [uu____1230]  in
                          uu____1217 :: uu____1226  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1215
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1209  in
                    let uu____1248 =
                      let uu____1252 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1252  in
                    FStar_Syntax_Util.abs uu____1248 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1259 = mk_lid "wp_close"  in
                    register env1 uu____1259 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    let uu____1270 =
                      let uu____1276 =
                        let uu____1277 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1277
                         in
                      FStar_Util.Inl uu____1276  in
                    Some uu____1270  in
                  let ret_gtot_type =
                    let uu____1297 =
                      let uu____1303 =
                        let uu____1304 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1304
                         in
                      FStar_Util.Inl uu____1303  in
                    Some uu____1297  in
                  let mk_forall1 x body =
                    let uu____1324 =
                      let uu____1327 =
                        let uu____1328 =
                          let uu____1338 =
                            let uu____1340 =
                              let uu____1341 =
                                let uu____1342 =
                                  let uu____1346 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1346]  in
                                FStar_Syntax_Util.abs uu____1342 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1341  in
                            [uu____1340]  in
                          (FStar_Syntax_Util.tforall, uu____1338)  in
                        FStar_Syntax_Syntax.Tm_app uu____1328  in
                      FStar_Syntax_Syntax.mk uu____1327  in
                    uu____1324 None FStar_Range.dummyRange  in
                  let rec is_discrete t =
                    let uu____1360 =
                      let uu____1361 = FStar_Syntax_Subst.compress t  in
                      uu____1361.FStar_Syntax_Syntax.n  in
                    match uu____1360 with
                    | FStar_Syntax_Syntax.Tm_type uu____1364 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1379  ->
                              match uu____1379 with
                              | (b,uu____1383) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1384 -> true  in
                  let rec is_monotonic t =
                    let uu____1389 =
                      let uu____1390 = FStar_Syntax_Subst.compress t  in
                      uu____1390.FStar_Syntax_Syntax.n  in
                    match uu____1389 with
                    | FStar_Syntax_Syntax.Tm_type uu____1393 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1408  ->
                              match uu____1408 with
                              | (b,uu____1412) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1413 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1465 =
                      let uu____1466 = FStar_Syntax_Subst.compress t1  in
                      uu____1466.FStar_Syntax_Syntax.n  in
                    match uu____1465 with
                    | FStar_Syntax_Syntax.Tm_type uu____1469 -> rel x y
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
                        let uu____1515 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1515
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2
                             in
                          let body =
                            let uu____1518 =
                              let uu____1521 =
                                let uu____1527 =
                                  let uu____1528 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1528  in
                                [uu____1527]  in
                              FStar_Syntax_Util.mk_app x uu____1521  in
                            let uu____1529 =
                              let uu____1532 =
                                let uu____1538 =
                                  let uu____1539 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1539  in
                                [uu____1538]  in
                              FStar_Syntax_Util.mk_app y uu____1532  in
                            mk_rel1 b uu____1518 uu____1529  in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2
                              in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2
                              in
                           let body =
                             let uu____1544 =
                               let uu____1545 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1548 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1545 uu____1548  in
                             let uu____1551 =
                               let uu____1552 =
                                 let uu____1555 =
                                   let uu____1561 =
                                     let uu____1562 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1562
                                      in
                                   [uu____1561]  in
                                 FStar_Syntax_Util.mk_app x uu____1555  in
                               let uu____1563 =
                                 let uu____1566 =
                                   let uu____1572 =
                                     let uu____1573 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1573
                                      in
                                   [uu____1572]  in
                                 FStar_Syntax_Util.mk_app y uu____1566  in
                               mk_rel1 b uu____1552 uu____1563  in
                             FStar_Syntax_Util.mk_imp uu____1544 uu____1551
                              in
                           let uu____1574 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1574)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___98_1595 = t1  in
                          let uu____1596 =
                            let uu____1597 =
                              let uu____1605 =
                                let uu____1606 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____1606  in
                              ([binder], uu____1605)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____1597  in
                          {
                            FStar_Syntax_Syntax.n = uu____1596;
                            FStar_Syntax_Syntax.tk =
                              (uu___98_1595.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___98_1595.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___98_1595.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1618 ->
                        failwith "unhandled arrow"
                    | uu____1626 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____1641 =
                        let uu____1642 = FStar_Syntax_Subst.compress t1  in
                        uu____1642.FStar_Syntax_Syntax.n  in
                      match uu____1641 with
                      | FStar_Syntax_Syntax.Tm_type uu____1645 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1662 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____1662
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1677 =
                                let uu____1678 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1678 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____1677
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)]
                             in
                          let uu____1699 =
                            let uu____1703 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1708  ->
                                     match uu____1708 with
                                     | (t2,q) ->
                                         let uu____1713 = project i x  in
                                         let uu____1714 = project i y  in
                                         mk_stronger t2 uu____1713 uu____1714)
                                args
                               in
                            match uu____1703 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____1699 with
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
                                 fun uu____1770  ->
                                   match uu____1770 with
                                   | (bv,q) ->
                                       let uu____1775 =
                                         let uu____1776 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____1776  in
                                       FStar_Syntax_Syntax.gen_bv uu____1775
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1780 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____1780) bvs
                             in
                          let body =
                            let uu____1782 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____1783 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____1782 uu____1783  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1786 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____1788 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____1789 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____1790 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____1788 uu____1789 uu____1790  in
                    let uu____1791 =
                      let uu____1795 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____1795  in
                    FStar_Syntax_Util.abs uu____1791 body ret_tot_type  in
                  let stronger1 =
                    let uu____1810 = mk_lid "stronger"  in
                    register env1 uu____1810 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let uu____1816 = FStar_Util.prefix gamma  in
                    match uu____1816 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (Prims.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____1842 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1842
                             in
                          let uu____1845 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____1845 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1853 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____1853  in
                              let guard_free1 =
                                let uu____1860 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____1860  in
                              let pat =
                                let uu____1864 =
                                  let uu____1870 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____1870]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1864
                                 in
                              let pattern_guarded_body =
                                let uu____1874 =
                                  let uu____1875 =
                                    let uu____1880 =
                                      let uu____1881 =
                                        let uu____1888 =
                                          let uu____1890 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____1890]  in
                                        [uu____1888]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1881
                                       in
                                    (body, uu____1880)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____1875  in
                                mk1 uu____1874  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1893 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____1896 =
                            let uu____1897 =
                              let uu____1898 =
                                let uu____1899 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____1902 =
                                  let uu____1908 = args_of_binders1 wp_args
                                     in
                                  let uu____1910 =
                                    let uu____1912 =
                                      let uu____1913 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____1913
                                       in
                                    [uu____1912]  in
                                  FStar_List.append uu____1908 uu____1910  in
                                FStar_Syntax_Util.mk_app uu____1899
                                  uu____1902
                                 in
                              FStar_Syntax_Util.mk_imp equiv uu____1898  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1897
                             in
                          FStar_Syntax_Util.abs gamma uu____1896
                            ret_gtot_type
                           in
                        let uu____1914 =
                          let uu____1918 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____1918  in
                        FStar_Syntax_Util.abs uu____1914 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____1925 = mk_lid "wp_ite"  in
                    register env1 uu____1925 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let uu____1931 = FStar_Util.prefix gamma  in
                    match uu____1931 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____1955 =
                            let uu____1956 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (Prims.fst post)
                               in
                            let uu____1959 =
                              let uu____1965 =
                                let uu____1966 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____1966  in
                              [uu____1965]  in
                            FStar_Syntax_Util.mk_app uu____1956 uu____1959
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1955
                           in
                        let uu____1967 =
                          let uu____1971 =
                            let uu____1975 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____1975 gamma  in
                          FStar_List.append binders uu____1971  in
                        FStar_Syntax_Util.abs uu____1967 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____1984 = mk_lid "null_wp"  in
                    register env1 uu____1984 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let body =
                      let uu____1993 =
                        let uu____1999 =
                          let uu____2001 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____2002 =
                            let uu____2004 =
                              let uu____2007 =
                                let uu____2013 =
                                  let uu____2014 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____2014  in
                                [uu____2013]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2007
                               in
                            let uu____2015 =
                              let uu____2019 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____2019]  in
                            uu____2004 :: uu____2015  in
                          uu____2001 :: uu____2002  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1999
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____1993  in
                    let uu____2022 =
                      let uu____2026 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____2026  in
                    FStar_Syntax_Util.abs uu____2022 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____2033 = mk_lid "wp_trivial"  in
                    register env1 uu____2033 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____2038 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____2038
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____2043 =
                      let uu____2045 = FStar_ST.read sigelts  in
                      FStar_List.rev uu____2045  in
                    let uu____2050 =
                      let uu___99_2051 = ed  in
                      let uu____2052 =
                        let uu____2053 = c wp_if_then_else2  in
                        ([], uu____2053)  in
                      let uu____2055 =
                        let uu____2056 = c wp_ite2  in ([], uu____2056)  in
                      let uu____2058 =
                        let uu____2059 = c stronger2  in ([], uu____2059)  in
                      let uu____2061 =
                        let uu____2062 = c wp_close2  in ([], uu____2062)  in
                      let uu____2064 =
                        let uu____2065 = c wp_assert2  in ([], uu____2065)
                         in
                      let uu____2067 =
                        let uu____2068 = c wp_assume2  in ([], uu____2068)
                         in
                      let uu____2070 =
                        let uu____2071 = c null_wp2  in ([], uu____2071)  in
                      let uu____2073 =
                        let uu____2074 = c wp_trivial2  in ([], uu____2074)
                         in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___99_2051.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___99_2051.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___99_2051.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___99_2051.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___99_2051.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___99_2051.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___99_2051.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___99_2051.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2052;
                        FStar_Syntax_Syntax.ite_wp = uu____2055;
                        FStar_Syntax_Syntax.stronger = uu____2058;
                        FStar_Syntax_Syntax.close_wp = uu____2061;
                        FStar_Syntax_Syntax.assert_p = uu____2064;
                        FStar_Syntax_Syntax.assume_p = uu____2067;
                        FStar_Syntax_Syntax.null_wp = uu____2070;
                        FStar_Syntax_Syntax.trivial = uu____2073;
                        FStar_Syntax_Syntax.repr =
                          (uu___99_2051.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___99_2051.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___99_2051.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___99_2051.FStar_Syntax_Syntax.actions)
                      }  in
                    (uu____2043, uu____2050)))))
  
type env_ = env
let get_env : env -> FStar_TypeChecker_Env.env = fun env  -> env.env 
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let uu___is_N : nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2090 -> false 
let __proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0 
let uu___is_M : nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2102 -> false 
let __proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let nm_of_comp : FStar_Syntax_Syntax.comp' -> nm =
  fun uu___86_2112  ->
    match uu___86_2112 with
    | FStar_Syntax_Syntax.Total (t,uu____2114) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___85_2123  ->
                match uu___85_2123 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2124 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2126 =
          let uu____2127 =
            let uu____2128 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2128
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2127  in
        failwith uu____2126
    | FStar_Syntax_Syntax.GTotal uu____2129 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let string_of_nm : nm -> Prims.string =
  fun uu___87_2137  ->
    match uu___87_2137 with
    | N t ->
        let uu____2139 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2139
    | M t ->
        let uu____2141 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2141
  
let is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2145,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2147;
                      FStar_Syntax_Syntax.pos = uu____2148;
                      FStar_Syntax_Syntax.vars = uu____2149;_})
        -> nm_of_comp n2
    | uu____2160 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let is_monadic_comp c =
  let uu____2172 = nm_of_comp c.FStar_Syntax_Syntax.n  in
  match uu____2172 with | M uu____2173 -> true | N uu____2174 -> false 
exception Not_found 
let uu___is_Not_found : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2178 -> false
  
let double_star :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2188 =
        let uu____2192 =
          let uu____2193 = FStar_Syntax_Syntax.new_bv None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2193  in
        [uu____2192]  in
      let uu____2194 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____2188 uu____2194  in
    let uu____2197 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____2197
  
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
          (let uu____2232 =
             let uu____2240 =
               let uu____2244 =
                 let uu____2247 =
                   let uu____2248 = star_type' env a  in
                   FStar_Syntax_Syntax.null_bv uu____2248  in
                 let uu____2249 = FStar_Syntax_Syntax.as_implicit false  in
                 (uu____2247, uu____2249)  in
               [uu____2244]  in
             let uu____2254 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
             (uu____2240, uu____2254)  in
           FStar_Syntax_Syntax.Tm_arrow uu____2232)

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2287) ->
          let binders1 =
            FStar_List.map
              (fun uu____2306  ->
                 match uu____2306 with
                 | (bv,aqual) ->
                     let uu____2313 =
                       let uu___100_2314 = bv  in
                       let uu____2315 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___100_2314.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___100_2314.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2315
                       }  in
                     (uu____2313, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2318,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2320);
                             FStar_Syntax_Syntax.tk = uu____2321;
                             FStar_Syntax_Syntax.pos = uu____2322;
                             FStar_Syntax_Syntax.vars = uu____2323;_})
               ->
               let uu____2340 =
                 let uu____2341 =
                   let uu____2349 =
                     let uu____2350 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____2350  in
                   (binders1, uu____2349)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____2341  in
               mk1 uu____2340
           | uu____2354 ->
               let uu____2355 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____2355 with
                | N hn ->
                    let uu____2357 =
                      let uu____2358 =
                        let uu____2366 =
                          let uu____2367 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____2367  in
                        (binders1, uu____2366)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____2358  in
                    mk1 uu____2357
                | M a ->
                    let uu____2372 =
                      let uu____2373 =
                        let uu____2381 =
                          let uu____2385 =
                            let uu____2389 =
                              let uu____2392 =
                                let uu____2393 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____2393  in
                              let uu____2394 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____2392, uu____2394)  in
                            [uu____2389]  in
                          FStar_List.append binders1 uu____2385  in
                        let uu____2401 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____2381, uu____2401)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____2373  in
                    mk1 uu____2372))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2452 = f x  in
                    FStar_Util.string_builder_append strb uu____2452);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2456 = f x1  in
                         FStar_Util.string_builder_append strb uu____2456))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____2458 = FStar_Syntax_Print.term_to_string t2  in
            let uu____2459 = string_of_set FStar_Syntax_Print.bv_to_string s
               in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2458 uu____2459
             in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2467 =
              let uu____2468 = FStar_Syntax_Subst.compress ty  in
              uu____2468.FStar_Syntax_Syntax.n  in
            match uu____2467 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2483 =
                  let uu____2484 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____2484  in
                if uu____2483
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2498 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____2498 s  in
                       let uu____2500 =
                         let uu____2501 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____2501  in
                       if uu____2500
                       then (debug1 ty1 sinter; Prims.raise Not_found)
                       else ()  in
                     let uu____2504 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____2504 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2515  ->
                                  match uu____2515 with
                                  | (bv,uu____2521) ->
                                      (non_dependent_or_raise s
                                         bv.FStar_Syntax_Syntax.sort;
                                       FStar_Util.set_add bv s))
                             FStar_Syntax_Syntax.no_names binders1
                            in
                         let ct = FStar_Syntax_Util.comp_result c1  in
                         (non_dependent_or_raise s ct;
                          (let k = n1 - (FStar_List.length binders1)  in
                           if k > (Prims.parse_int "0")
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found  -> false)
            | uu____2534 ->
                ((let uu____2536 = FStar_Syntax_Print.term_to_string ty  in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2536);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____2541 =
              let uu____2542 = FStar_Syntax_Subst.compress head2  in
              uu____2542.FStar_Syntax_Syntax.n  in
            match uu____2541 with
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
                  (let uu____2546 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____2546)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2559 -> true
                 | uu____2569 ->
                     ((let uu____2571 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2571);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
                true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2575) ->
                is_valid_application t2
            | uu____2580 -> false  in
          let uu____2581 = is_valid_application head1  in
          if uu____2581
          then
            let uu____2582 =
              let uu____2583 =
                let uu____2593 =
                  FStar_List.map
                    (fun uu____2603  ->
                       match uu____2603 with
                       | (t2,qual) ->
                           let uu____2616 = star_type' env t2  in
                           (uu____2616, qual)) args
                   in
                (head1, uu____2593)  in
              FStar_Syntax_Syntax.Tm_app uu____2583  in
            mk1 uu____2582
          else
            (let uu____2623 =
               let uu____2624 =
                 let uu____2625 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2625
                  in
               FStar_Errors.Err uu____2624  in
             Prims.raise uu____2623)
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_name _
         |FStar_Syntax_Syntax.Tm_type _|FStar_Syntax_Syntax.Tm_fvar _ -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2655 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____2655 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___103_2661 = env  in
                 let uu____2662 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____2662;
                   subst = (uu___103_2661.subst);
                   tc_const = (uu___103_2661.tc_const)
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
               ((let uu___104_2679 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___104_2679.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___104_2679.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2686 =
            let uu____2687 =
              let uu____2692 = star_type' env t2  in (uu____2692, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____2687  in
          mk1 uu____2686
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2730 =
            let uu____2731 =
              let uu____2749 = star_type' env e  in
              let uu____2750 =
                let uu____2760 =
                  let uu____2765 = star_type' env t2  in
                  FStar_Util.Inl uu____2765  in
                (uu____2760, None)  in
              (uu____2749, uu____2750, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2731  in
          mk1 uu____2730
      | FStar_Syntax_Syntax.Tm_ascribed uu____2787 ->
          let uu____2805 =
            let uu____2806 =
              let uu____2807 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2807
               in
            FStar_Errors.Err uu____2806  in
          Prims.raise uu____2805
      | FStar_Syntax_Syntax.Tm_refine uu____2808 ->
          let uu____2813 =
            let uu____2814 =
              let uu____2815 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2815
               in
            FStar_Errors.Err uu____2814  in
          Prims.raise uu____2813
      | FStar_Syntax_Syntax.Tm_uinst uu____2816 ->
          let uu____2821 =
            let uu____2822 =
              let uu____2823 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2823
               in
            FStar_Errors.Err uu____2822  in
          Prims.raise uu____2821
      | FStar_Syntax_Syntax.Tm_constant uu____2824 ->
          let uu____2825 =
            let uu____2826 =
              let uu____2827 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2827
               in
            FStar_Errors.Err uu____2826  in
          Prims.raise uu____2825
      | FStar_Syntax_Syntax.Tm_match uu____2828 ->
          let uu____2844 =
            let uu____2845 =
              let uu____2846 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2846
               in
            FStar_Errors.Err uu____2845  in
          Prims.raise uu____2844
      | FStar_Syntax_Syntax.Tm_let uu____2847 ->
          let uu____2855 =
            let uu____2856 =
              let uu____2857 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2857
               in
            FStar_Errors.Err uu____2856  in
          Prims.raise uu____2855
      | FStar_Syntax_Syntax.Tm_uvar uu____2858 ->
          let uu____2867 =
            let uu____2868 =
              let uu____2869 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2869
               in
            FStar_Errors.Err uu____2868  in
          Prims.raise uu____2867
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2870 =
            let uu____2871 =
              let uu____2872 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2872
               in
            FStar_Errors.Err uu____2871  in
          Prims.raise uu____2870
      | FStar_Syntax_Syntax.Tm_delayed uu____2873 -> failwith "impossible"

let is_monadic uu___89_2906 =
  match uu___89_2906 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
    { FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _;
      FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _;_})
    |Some (FStar_Util.Inr (_,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___88_2943  ->
              match uu___88_2943 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____2944 -> false))
  
let rec is_C : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2948 =
      let uu____2949 = FStar_Syntax_Subst.compress t  in
      uu____2949.FStar_Syntax_Syntax.n  in
    match uu____2948 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2969 =
            let uu____2970 = FStar_List.hd args  in Prims.fst uu____2970  in
          is_C uu____2969  in
        if r
        then
          ((let uu____2982 =
              let uu____2983 =
                FStar_List.for_all
                  (fun uu____2986  ->
                     match uu____2986 with | (h,uu____2990) -> is_C h) args
                 in
              Prims.op_Negation uu____2983  in
            if uu____2982 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2994 =
              let uu____2995 =
                FStar_List.for_all
                  (fun uu____2998  ->
                     match uu____2998 with
                     | (h,uu____3002) ->
                         let uu____3003 = is_C h  in
                         Prims.op_Negation uu____3003) args
                 in
              Prims.op_Negation uu____2995  in
            if uu____2994 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____3017 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____3017 with
         | M t1 ->
             ((let uu____3020 = is_C t1  in
               if uu____3020 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,_)
      |FStar_Syntax_Syntax.Tm_uinst (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
       (t1,_,_) -> is_C t1
    | uu____3052 -> false
  
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
          let uu____3083 =
            let uu____3084 =
              let uu____3094 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____3095 =
                let uu____3099 =
                  let uu____3102 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____3102)  in
                [uu____3099]  in
              (uu____3094, uu____3095)  in
            FStar_Syntax_Syntax.Tm_app uu____3084  in
          mk1 uu____3083  in
        let uu____3110 =
          let uu____3114 = FStar_Syntax_Syntax.mk_binder p  in [uu____3114]
           in
        let uu____3115 =
          let uu____3122 =
            let uu____3128 =
              let uu____3129 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
              FStar_Syntax_Util.lcomp_of_comp uu____3129  in
            FStar_Util.Inl uu____3128  in
          Some uu____3122  in
        FStar_Syntax_Util.abs uu____3110 body uu____3115
  
let is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___90_3142  ->
    match uu___90_3142 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3143 -> false
  
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
        let return_if uu____3287 =
          match uu____3287 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3308 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3309 =
                       let uu____3310 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____3310  in
                     Prims.op_Negation uu____3309)
                   in
                if uu____3308
                then
                  let uu____3311 =
                    let uu____3312 =
                      let uu____3313 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____3314 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____3315 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3313 uu____3314 uu____3315
                       in
                    FStar_Errors.Err uu____3312  in
                  Prims.raise uu____3311
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2)|(M t1,M t2) ->
                   (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3326 = mk_return env t1 s_e  in
                     ((M t1), uu____3326, u_e)))
               | (M t1,N t2) ->
                   let uu____3329 =
                     let uu____3330 =
                       let uu____3331 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____3332 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____3333 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3331 uu____3332 uu____3333
                        in
                     FStar_Errors.Err uu____3330  in
                   Prims.raise uu____3329)
           in
        let ensure_m env1 e2 =
          let strip_m uu___91_3359 =
            match uu___91_3359 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3369 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____3380 =
                let uu____3381 =
                  let uu____3384 =
                    let uu____3385 = FStar_Syntax_Print.term_to_string t  in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3385
                     in
                  (uu____3384, (e2.FStar_Syntax_Syntax.pos))  in
                FStar_Errors.Error uu____3381  in
              Prims.raise uu____3380
          | M uu____3389 ->
              let uu____3390 = check env1 e2 context_nm  in
              strip_m uu____3390
           in
        let uu____3394 =
          let uu____3395 = FStar_Syntax_Subst.compress e  in
          uu____3395.FStar_Syntax_Syntax.n  in
        match uu____3394 with
        | FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_name _
           |FStar_Syntax_Syntax.Tm_fvar _
            |FStar_Syntax_Syntax.Tm_abs _
             |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_app _
            -> let uu____3407 = infer env e  in return_if uu____3407
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
        | FStar_Syntax_Syntax.Tm_let uu____3482 ->
            let uu____3490 =
              let uu____3491 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3491  in
            failwith uu____3490
        | FStar_Syntax_Syntax.Tm_type uu____3495 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3499 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3510 ->
            let uu____3515 =
              let uu____3516 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3516  in
            failwith uu____3515
        | FStar_Syntax_Syntax.Tm_uvar uu____3520 ->
            let uu____3529 =
              let uu____3530 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3530  in
            failwith uu____3529
        | FStar_Syntax_Syntax.Tm_delayed uu____3534 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3558 =
              let uu____3559 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3559  in
            failwith uu____3558

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
      let uu____3581 =
        let uu____3582 = FStar_Syntax_Subst.compress e  in
        uu____3582.FStar_Syntax_Syntax.n  in
      match uu____3581 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let env1 =
            let uu___105_3622 = env  in
            let uu____3623 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____3623;
              subst = (uu___105_3622.subst);
              tc_const = (uu___105_3622.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____3632  ->
                 match uu____3632 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___106_3640 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___106_3640.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___106_3640.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____3641 =
            FStar_List.fold_left
              (fun uu____3650  ->
                 fun uu____3651  ->
                   match (uu____3650, uu____3651) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____3679 = is_C c  in
                       if uu____3679
                       then
                         let xw =
                           let uu____3684 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "^w") None uu____3684
                            in
                         let x =
                           let uu___107_3686 = bv  in
                           let uu____3687 =
                             let uu____3690 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____3690  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___107_3686.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___107_3686.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3687
                           }  in
                         let env3 =
                           let uu___108_3692 = env2  in
                           let uu____3693 =
                             let uu____3695 =
                               let uu____3696 =
                                 let uu____3701 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____3701)  in
                               FStar_Syntax_Syntax.NT uu____3696  in
                             uu____3695 :: (env2.subst)  in
                           {
                             env = (uu___108_3692.env);
                             subst = uu____3693;
                             tc_const = (uu___108_3692.tc_const)
                           }  in
                         let uu____3702 =
                           let uu____3704 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____3705 =
                             let uu____3707 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____3707 :: acc  in
                           uu____3704 :: uu____3705  in
                         (env3, uu____3702)
                       else
                         (let x =
                            let uu___109_3711 = bv  in
                            let uu____3712 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___109_3711.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___109_3711.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3712
                            }  in
                          let uu____3715 =
                            let uu____3717 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____3717 :: acc  in
                          (env2, uu____3715))) (env1, []) binders1
             in
          (match uu____3641 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____3729 =
                 let check_what =
                   let uu____3741 = is_monadic what  in
                   if uu____3741 then check_m else check_n  in
                 let uu____3750 = check_what env2 body1  in
                 match uu____3750 with
                 | (t,s_body,u_body) ->
                     let uu____3760 =
                       let uu____3761 =
                         let uu____3762 = is_monadic what  in
                         if uu____3762 then M t else N t  in
                       comp_of_nm uu____3761  in
                     (uu____3760, s_body, u_body)
                  in
               (match uu____3729 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3805 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___92_3807  ->
                                    match uu___92_3807 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3808 -> false))
                             in
                          if uu____3805
                          then
                            let double_starred_comp =
                              let uu____3816 =
                                let uu____3817 =
                                  let uu____3818 =
                                    lc.FStar_Syntax_Syntax.comp ()  in
                                  FStar_Syntax_Util.comp_result uu____3818
                                   in
                                FStar_All.pipe_left double_star uu____3817
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____3816  in
                            let flags =
                              FStar_List.filter
                                (fun uu___93_3823  ->
                                   match uu___93_3823 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3824 -> true)
                                lc.FStar_Syntax_Syntax.cflags
                               in
                            let uu____3825 =
                              let uu____3831 =
                                let uu____3832 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags
                                   in
                                FStar_Syntax_Util.lcomp_of_comp uu____3832
                                 in
                              FStar_Util.Inl uu____3831  in
                            Some uu____3825
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___110_3852 = lc  in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___110_3852.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___110_3852.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___110_3852.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____3853  ->
                                          let c =
                                            lc.FStar_Syntax_Syntax.comp ()
                                             in
                                          let result_typ =
                                            star_type' env2
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          FStar_Syntax_Util.set_result_typ c
                                            result_typ)
                                   })))
                      | Some (FStar_Util.Inr (lid,flags)) ->
                          let uu____3870 =
                            let uu____3876 =
                              let uu____3880 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___94_3882  ->
                                        match uu___94_3882 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____3883 -> false))
                                 in
                              if uu____3880
                              then
                                let uu____3887 =
                                  FStar_List.filter
                                    (fun uu___95_3889  ->
                                       match uu___95_3889 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____3890 -> true) flags
                                   in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____3887)
                              else (lid, flags)  in
                            FStar_Util.Inr uu____3876  in
                          Some uu____3870
                       in
                    let uu____3902 =
                      let comp1 =
                        let uu____3914 = is_monadic what  in
                        let uu____3915 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3914 uu____3915
                         in
                      let uu____3916 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None)
                         in
                      (uu____3916,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1))))
                       in
                    (match uu____3902 with
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
                FStar_Syntax_Syntax.ty = uu____3994;
                FStar_Syntax_Syntax.p = uu____3995;_};
            FStar_Syntax_Syntax.fv_delta = uu____3996;
            FStar_Syntax_Syntax.fv_qual = uu____3997;_}
          ->
          let uu____4003 =
            let uu____4006 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left Prims.fst uu____4006  in
          (match uu____4003 with
           | (uu____4022,t) ->
               let uu____4024 =
                 let uu____4025 = normalize1 t  in N uu____4025  in
               (uu____4024, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____4042 = check_n env head1  in
          (match uu____4042 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4056 =
                   let uu____4057 = FStar_Syntax_Subst.compress t  in
                   uu____4057.FStar_Syntax_Syntax.n  in
                 match uu____4056 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4060 -> true
                 | uu____4068 -> false  in
               let rec flatten1 t =
                 let uu____4080 =
                   let uu____4081 = FStar_Syntax_Subst.compress t  in
                   uu____4081.FStar_Syntax_Syntax.n  in
                 match uu____4080 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4093);
                                FStar_Syntax_Syntax.tk = uu____4094;
                                FStar_Syntax_Syntax.pos = uu____4095;
                                FStar_Syntax_Syntax.vars = uu____4096;_})
                     when is_arrow t1 ->
                     let uu____4113 = flatten1 t1  in
                     (match uu____4113 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4165,uu____4166)
                     -> flatten1 e1
                 | uu____4195 ->
                     let uu____4196 =
                       let uu____4197 =
                         let uu____4198 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4198
                          in
                       FStar_Errors.Err uu____4197  in
                     Prims.raise uu____4196
                  in
               let uu____4206 = flatten1 t_head  in
               (match uu____4206 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4251 =
                          let uu____4252 =
                            let uu____4253 = FStar_Util.string_of_int n1  in
                            let uu____4257 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____4263 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4253 uu____4257 uu____4263
                             in
                          FStar_Errors.Err uu____4252  in
                        Prims.raise uu____4251)
                     else ();
                     (let uu____4268 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____4268 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4295 args1 =
                            match uu____4295 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4338 =
                                       let uu____4339 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____4339.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____4338
                                 | (binders3,[]) ->
                                     let uu____4358 =
                                       let uu____4359 =
                                         let uu____4362 =
                                           let uu____4363 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4363
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____4362
                                          in
                                       uu____4359.FStar_Syntax_Syntax.n  in
                                     (match uu____4358 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4379 =
                                            let uu____4380 =
                                              let uu____4381 =
                                                let uu____4389 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____4389)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4381
                                               in
                                            mk1 uu____4380  in
                                          N uu____4379
                                      | uu____4393 -> failwith "wat?")
                                 | ([],uu____4394::uu____4395) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4420)::binders3,(arg,uu____4423)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____4457 = FStar_List.splitAt n' binders1  in
                          (match uu____4457 with
                           | (binders2,uu____4474) ->
                               let uu____4487 =
                                 let uu____4497 =
                                   FStar_List.map2
                                     (fun uu____4517  ->
                                        fun uu____4518  ->
                                          match (uu____4517, uu____4518) with
                                          | ((bv,uu____4535),(arg,q)) ->
                                              let uu____4542 =
                                                let uu____4543 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____4543.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____4542 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4553 ->
                                                   let arg1 = (arg, q)  in
                                                   (arg1, [arg1])
                                               | uu____4566 ->
                                                   let uu____4567 =
                                                     check_n env arg  in
                                                   (match uu____4567 with
                                                    | (uu____4578,s_arg,u_arg)
                                                        ->
                                                        let uu____4581 =
                                                          let uu____4585 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____4585
                                                          then
                                                            let uu____4589 =
                                                              let uu____4592
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____4592, q)
                                                               in
                                                            [uu____4589;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____4581))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____4497  in
                               (match uu____4487 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____4639 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____4645 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____4639, uu____4645)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,_)
        |FStar_Syntax_Syntax.Tm_meta (e1,_)|FStar_Syntax_Syntax.Tm_ascribed
         (e1,_,_) -> infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4723 = let uu____4724 = env.tc_const c  in N uu____4724
             in
          (uu____4723, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4725 ->
          let uu____4733 =
            let uu____4734 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4734  in
          failwith uu____4733
      | FStar_Syntax_Syntax.Tm_type uu____4738 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4742 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4753 ->
          let uu____4758 =
            let uu____4759 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4759  in
          failwith uu____4758
      | FStar_Syntax_Syntax.Tm_uvar uu____4763 ->
          let uu____4772 =
            let uu____4773 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4773  in
          failwith uu____4772
      | FStar_Syntax_Syntax.Tm_delayed uu____4777 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4801 =
            let uu____4802 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4802  in
          failwith uu____4801

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
          let uu____4840 = check_n env e0  in
          match uu____4840 with
          | (uu____4847,s_e0,u_e0) ->
              let uu____4850 =
                let uu____4868 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4901 = FStar_Syntax_Subst.open_branch b  in
                       match uu____4901 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___111_4933 = env  in
                             let uu____4934 =
                               let uu____4935 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4935
                                in
                             {
                               env = uu____4934;
                               subst = (uu___111_4933.subst);
                               tc_const = (uu___111_4933.tc_const)
                             }  in
                           let uu____4937 = f env1 body  in
                           (match uu____4937 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4986 ->
                           Prims.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____4868  in
              (match uu____4850 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5051 = FStar_List.hd nms  in
                     match uu____5051 with | M t1|N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___96_5054  ->
                          match uu___96_5054 with
                          | M uu____5055 -> true
                          | uu____5056 -> false) nms
                      in
                   let uu____5057 =
                     let uu____5080 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5132  ->
                              match uu____5132 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false )|(M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5228 =
                                         check env original_body (M t2)  in
                                       (match uu____5228 with
                                        | (uu____5251,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5280,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____5080  in
                   (match uu____5057 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5399  ->
                                 match uu____5399 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5440 =
                                         let uu____5441 =
                                           let uu____5451 =
                                             let uu____5455 =
                                               let uu____5458 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____5459 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____5458, uu____5459)  in
                                             [uu____5455]  in
                                           (s_body, uu____5451)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5441
                                          in
                                       mk1 uu____5440  in
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
                            let uu____5481 =
                              let uu____5485 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____5485]  in
                            let uu____5486 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            let uu____5488 =
                              let uu____5495 =
                                let uu____5501 =
                                  let uu____5502 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0
                                     in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5502
                                   in
                                FStar_Util.Inl uu____5501  in
                              Some uu____5495  in
                            FStar_Syntax_Util.abs uu____5481 uu____5486
                              uu____5488
                             in
                          let t1_star =
                            let uu____5516 =
                              let uu____5520 =
                                let uu____5521 =
                                  FStar_Syntax_Syntax.new_bv None p_type  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5521
                                 in
                              [uu____5520]  in
                            let uu____5522 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____5516 uu____5522  in
                          let uu____5525 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None))
                             in
                          let uu____5555 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____5525, uu____5555)
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
                           let uu____5569 =
                             let uu____5572 =
                               let uu____5573 =
                                 let uu____5591 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____5591,
                                   ((FStar_Util.Inl t1_star), None), None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5573  in
                             mk1 uu____5572  in
                           let uu____5618 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____5569, uu____5618))))

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
              let uu____5661 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____5661]  in
            let uu____5662 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____5662 with
            | (x_binders1,e21) ->
                let uu____5670 = infer env e1  in
                (match uu____5670 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5681 = is_C t1  in
                       if uu____5681
                       then
                         let uu___112_5682 = binding  in
                         let uu____5683 =
                           let uu____5686 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____5686  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___112_5682.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___112_5682.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5683;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___112_5682.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___112_5682.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding  in
                     let env1 =
                       let uu___113_5689 = env  in
                       let uu____5690 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___114_5691 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___114_5691.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___114_5691.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____5690;
                         subst = (uu___113_5689.subst);
                         tc_const = (uu___113_5689.tc_const)
                       }  in
                     let uu____5692 = proceed env1 e21  in
                     (match uu____5692 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___115_5703 = binding  in
                            let uu____5704 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___115_5703.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___115_5703.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5704;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___115_5703.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___115_5703.FStar_Syntax_Syntax.lbdef)
                            }  in
                          let uu____5707 =
                            let uu____5710 =
                              let uu____5711 =
                                let uu____5719 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___116_5724 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___116_5724.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___116_5724.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___116_5724.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___116_5724.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5719)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5711  in
                            mk1 uu____5710  in
                          let uu____5725 =
                            let uu____5728 =
                              let uu____5729 =
                                let uu____5737 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___117_5742 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___117_5742.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___117_5742.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___117_5742.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___117_5742.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5737)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5729  in
                            mk1 uu____5728  in
                          (nm_rec, uu____5707, uu____5725))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___118_5751 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___118_5751.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___118_5751.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___118_5751.FStar_Syntax_Syntax.lbdef)
                       }  in
                     let env1 =
                       let uu___119_5753 = env  in
                       let uu____5754 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___120_5755 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___120_5755.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___120_5755.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____5754;
                         subst = (uu___119_5753.subst);
                         tc_const = (uu___119_5753.tc_const)
                       }  in
                     let uu____5756 = ensure_m env1 e21  in
                     (match uu____5756 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_e21 =
                            let uu____5773 =
                              let uu____5774 =
                                let uu____5784 =
                                  let uu____5788 =
                                    let uu____5791 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____5792 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____5791, uu____5792)  in
                                  [uu____5788]  in
                                (s_e2, uu____5784)  in
                              FStar_Syntax_Syntax.Tm_app uu____5774  in
                            mk1 uu____5773  in
                          let s_e22 =
                            let uu____5801 =
                              let uu____5808 =
                                let uu____5814 =
                                  let uu____5815 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0
                                     in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5815
                                   in
                                FStar_Util.Inl uu____5814  in
                              Some uu____5808  in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____5801
                             in
                          let body =
                            let uu____5829 =
                              let uu____5830 =
                                let uu____5840 =
                                  let uu____5844 =
                                    let uu____5847 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____5847)  in
                                  [uu____5844]  in
                                (s_e1, uu____5840)  in
                              FStar_Syntax_Syntax.Tm_app uu____5830  in
                            mk1 uu____5829  in
                          let uu____5855 =
                            let uu____5856 =
                              let uu____5860 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____5860]  in
                            let uu____5861 =
                              let uu____5868 =
                                let uu____5874 =
                                  let uu____5875 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0
                                     in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5875
                                   in
                                FStar_Util.Inl uu____5874  in
                              Some uu____5868  in
                            FStar_Syntax_Util.abs uu____5856 body uu____5861
                             in
                          let uu____5886 =
                            let uu____5889 =
                              let uu____5890 =
                                let uu____5898 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___121_5903 = u_binding  in
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
                                     })]), uu____5898)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5890  in
                            mk1 uu____5889  in
                          ((M t2), uu____5855, uu____5886)))

and check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5912 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos
           in
        N uu____5912  in
      let uu____5917 = check env e mn  in
      match uu____5917 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5927 -> failwith "[check_n]: impossible"

and check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5940 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos
           in
        M uu____5940  in
      let uu____5945 = check env e mn  in
      match uu____5945 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5955 -> failwith "[check_m]: impossible"

and comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp =
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

and type_of_comp :
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> FStar_Syntax_Util.comp_result t

and trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____5977 =
           let uu____5978 = is_C c  in Prims.op_Negation uu____5978  in
         if uu____5977 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos
            in
         let uu____5990 =
           let uu____5991 = FStar_Syntax_Subst.compress c  in
           uu____5991.FStar_Syntax_Syntax.n  in
         match uu____5990 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____6010 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____6010 with
              | (wp_head,wp_args) ->
                  ((let uu____6037 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6050 =
                           let uu____6051 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6051
                            in
                         Prims.op_Negation uu____6050)
                       in
                    if uu____6037 then failwith "mismatch" else ());
                   (let uu____6060 =
                      let uu____6061 =
                        let uu____6071 =
                          FStar_List.map2
                            (fun uu____6081  ->
                               fun uu____6082  ->
                                 match (uu____6081, uu____6082) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6105 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____6105
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____6108 = print_implicit q
                                            in
                                         let uu____6109 = print_implicit q'
                                            in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6108 uu____6109)
                                      else ();
                                      (let uu____6111 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____6111, q)))) args wp_args
                           in
                        (head1, uu____6071)  in
                      FStar_Syntax_Syntax.Tm_app uu____6061  in
                    mk1 uu____6060)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____6133 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____6133 with
              | (binders_orig,comp1) ->
                  let uu____6138 =
                    let uu____6146 =
                      FStar_List.map
                        (fun uu____6160  ->
                           match uu____6160 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____6173 = is_C h  in
                               if uu____6173
                               then
                                 let w' =
                                   let uu____6180 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "-w'") None uu____6180
                                    in
                                 let uu____6181 =
                                   let uu____6185 =
                                     let uu____6189 =
                                       let uu____6192 =
                                         let uu____6193 =
                                           let uu____6194 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____6194  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6193
                                          in
                                       (uu____6192, q)  in
                                     [uu____6189]  in
                                   (w', q) :: uu____6185  in
                                 (w', uu____6181)
                               else
                                 (let x =
                                    let uu____6206 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "-x") None uu____6206
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____6146  in
                  (match uu____6138 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____6236 =
                           let uu____6238 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6238
                            in
                         FStar_Syntax_Subst.subst_comp uu____6236 comp1  in
                       let app =
                         let uu____6242 =
                           let uu____6243 =
                             let uu____6253 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6260 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____6261 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____6260, uu____6261)) bvs
                                in
                             (wp, uu____6253)  in
                           FStar_Syntax_Syntax.Tm_app uu____6243  in
                         mk1 uu____6242  in
                       let comp3 =
                         let uu____6266 = type_of_comp comp2  in
                         let uu____6267 = is_monadic_comp comp2  in
                         trans_G env uu____6266 uu____6267 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6269,uu____6270) ->
             trans_F_ env e wp
         | uu____6299 -> failwith "impossible trans_F_")

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
            let uu____6314 =
              let uu____6315 = star_type' env h  in
              let uu____6318 =
                let uu____6324 =
                  let uu____6327 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____6327)  in
                [uu____6324]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6315;
                FStar_Syntax_Syntax.effect_args = uu____6318;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____6314
          else
            (let uu____6333 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____6333)

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
    fun t  -> let uu____6344 = n env.env t  in star_type' env uu____6344
  
let star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6356 = n env.env t  in check_n env uu____6356
  
let trans_F :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6366 = n env.env c  in
        let uu____6367 = n env.env wp  in trans_F_ env uu____6366 uu____6367
  