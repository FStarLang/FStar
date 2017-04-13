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
                      let uu____289 =
                        let uu____293 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____294 =
                          let uu____296 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____296]  in
                        uu____293 :: uu____294  in
                      FStar_List.append binders uu____289  in
                    FStar_Syntax_Util.abs uu____288 body None  in
                  let uu____304 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____305 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____304, uu____305)  in
                match uu____265 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
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
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____367 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____366, uu____367)) binders
                               in
                            let uu____368 =
                              let uu____372 =
                                let uu____375 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____376 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____375, uu____376)  in
                              let uu____377 =
                                let uu____381 =
                                  let uu____384 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____384)  in
                                [uu____381]  in
                              uu____372 :: uu____377  in
                            FStar_List.append uu____351 uu____368  in
                          (fv, uu____347)  in
                        FStar_Syntax_Syntax.Tm_app uu____337  in
                      mk1 uu____336  in
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
                      let uu____430 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x" None uu____430  in
                    let ret1 =
                      let uu____438 =
                        let uu____444 =
                          let uu____445 =
                            let uu____448 =
                              let uu____449 =
                                FStar_Syntax_Syntax.bv_to_name t  in
                              mk_ctx uu____449  in
                            FStar_Syntax_Syntax.mk_Total uu____448  in
                          FStar_Syntax_Util.lcomp_of_comp uu____445  in
                        FStar_Util.Inl uu____444  in
                      Some uu____438  in
                    let body =
                      let uu____459 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____459 ret1  in
                    let uu____460 =
                      let uu____461 = mk_all_implicit binders  in
                      let uu____465 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____461 uu____465  in
                    FStar_Syntax_Util.abs uu____460 body ret1  in
                  let c_pure1 =
                    let uu____480 = mk_lid "pure"  in
                    register env1 uu____480 c_pure  in
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
                      let uu____485 =
                        let uu____486 =
                          let uu____487 =
                            let uu____491 =
                              let uu____492 =
                                let uu____493 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv None uu____493  in
                              FStar_Syntax_Syntax.mk_binder uu____492  in
                            [uu____491]  in
                          let uu____494 =
                            let uu____497 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____497  in
                          FStar_Syntax_Util.arrow uu____487 uu____494  in
                        mk_gctx uu____486  in
                      FStar_Syntax_Syntax.gen_bv "l" None uu____485  in
                    let r =
                      let uu____499 =
                        let uu____500 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____500  in
                      FStar_Syntax_Syntax.gen_bv "r" None uu____499  in
                    let ret1 =
                      let uu____508 =
                        let uu____514 =
                          let uu____515 =
                            let uu____518 =
                              let uu____519 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              mk_gctx uu____519  in
                            FStar_Syntax_Syntax.mk_Total uu____518  in
                          FStar_Syntax_Util.lcomp_of_comp uu____515  in
                        FStar_Util.Inl uu____514  in
                      Some uu____508  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____534 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____537 =
                          let uu____543 =
                            let uu____545 =
                              let uu____546 =
                                let uu____547 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____547
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____546  in
                            [uu____545]  in
                          FStar_List.append gamma_as_args uu____543  in
                        FStar_Syntax_Util.mk_app uu____534 uu____537  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____550 =
                      let uu____551 = mk_all_implicit binders  in
                      let uu____555 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____551 uu____555  in
                    FStar_Syntax_Util.abs uu____550 outer_body ret1  in
                  let c_app1 =
                    let uu____574 = mk_lid "app"  in
                    register env1 uu____574 c_app  in
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
                      let uu____581 =
                        let uu____585 =
                          let uu____586 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____586  in
                        [uu____585]  in
                      let uu____587 =
                        let uu____590 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____590  in
                      FStar_Syntax_Util.arrow uu____581 uu____587  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a11 =
                      let uu____593 =
                        let uu____594 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____594  in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____593  in
                    let ret1 =
                      let uu____602 =
                        let uu____608 =
                          let uu____609 =
                            let uu____612 =
                              let uu____613 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              mk_gctx uu____613  in
                            FStar_Syntax_Syntax.mk_Total uu____612  in
                          FStar_Syntax_Util.lcomp_of_comp uu____609  in
                        FStar_Util.Inl uu____608  in
                      Some uu____602  in
                    let uu____622 =
                      let uu____623 = mk_all_implicit binders  in
                      let uu____627 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____623 uu____627  in
                    let uu____645 =
                      let uu____646 =
                        let uu____652 =
                          let uu____654 =
                            let uu____657 =
                              let uu____663 =
                                let uu____665 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____665]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____663
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____657  in
                          let uu____666 =
                            let uu____670 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____670]  in
                          uu____654 :: uu____666  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____652
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____646  in
                    FStar_Syntax_Util.abs uu____622 uu____645 ret1  in
                  let c_lift11 =
                    let uu____674 = mk_lid "lift1"  in
                    register env1 uu____674 c_lift1  in
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
                      let uu____682 =
                        let uu____686 =
                          let uu____687 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____687  in
                        let uu____688 =
                          let uu____690 =
                            let uu____691 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.null_binder uu____691  in
                          [uu____690]  in
                        uu____686 :: uu____688  in
                      let uu____692 =
                        let uu____695 = FStar_Syntax_Syntax.bv_to_name t3  in
                        FStar_Syntax_Syntax.mk_GTotal uu____695  in
                      FStar_Syntax_Util.arrow uu____682 uu____692  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let a11 =
                      let uu____698 =
                        let uu____699 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____699  in
                      FStar_Syntax_Syntax.gen_bv "a1" None uu____698  in
                    let a2 =
                      let uu____701 =
                        let uu____702 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____702  in
                      FStar_Syntax_Syntax.gen_bv "a2" None uu____701  in
                    let ret1 =
                      let uu____710 =
                        let uu____716 =
                          let uu____717 =
                            let uu____720 =
                              let uu____721 =
                                FStar_Syntax_Syntax.bv_to_name t3  in
                              mk_gctx uu____721  in
                            FStar_Syntax_Syntax.mk_Total uu____720  in
                          FStar_Syntax_Util.lcomp_of_comp uu____717  in
                        FStar_Util.Inl uu____716  in
                      Some uu____710  in
                    let uu____730 =
                      let uu____731 = mk_all_implicit binders  in
                      let uu____735 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____731 uu____735  in
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
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____788]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____786
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____780
                                   in
                                let uu____789 =
                                  let uu____793 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____793]  in
                                uu____777 :: uu____789  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____775
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____769  in
                          let uu____796 =
                            let uu____800 = FStar_Syntax_Syntax.bv_to_name a2
                               in
                            [uu____800]  in
                          uu____766 :: uu____796  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____764
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____758  in
                    FStar_Syntax_Util.abs uu____730 uu____757 ret1  in
                  let c_lift21 =
                    let uu____804 = mk_lid "lift2"  in
                    register env1 uu____804 c_lift2  in
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
                      let uu____811 =
                        let uu____815 =
                          let uu____816 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____816  in
                        [uu____815]  in
                      let uu____817 =
                        let uu____820 =
                          let uu____821 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____821  in
                        FStar_Syntax_Syntax.mk_Total uu____820  in
                      FStar_Syntax_Util.arrow uu____811 uu____817  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let ret1 =
                      let uu____830 =
                        let uu____836 =
                          let uu____837 =
                            let uu____840 =
                              let uu____841 =
                                let uu____842 =
                                  let uu____846 =
                                    let uu____847 =
                                      FStar_Syntax_Syntax.bv_to_name t1  in
                                    FStar_Syntax_Syntax.null_binder uu____847
                                     in
                                  [uu____846]  in
                                let uu____848 =
                                  let uu____851 =
                                    FStar_Syntax_Syntax.bv_to_name t2  in
                                  FStar_Syntax_Syntax.mk_GTotal uu____851  in
                                FStar_Syntax_Util.arrow uu____842 uu____848
                                 in
                              mk_ctx uu____841  in
                            FStar_Syntax_Syntax.mk_Total uu____840  in
                          FStar_Syntax_Util.lcomp_of_comp uu____837  in
                        FStar_Util.Inl uu____836  in
                      Some uu____830  in
                    let e1 =
                      let uu____861 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1" None uu____861  in
                    let body =
                      let uu____863 =
                        let uu____864 =
                          let uu____868 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____868]  in
                        FStar_List.append gamma uu____864  in
                      let uu____871 =
                        let uu____872 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____875 =
                          let uu____881 =
                            let uu____882 = FStar_Syntax_Syntax.bv_to_name e1
                               in
                            FStar_Syntax_Syntax.as_arg uu____882  in
                          let uu____883 = args_of_binders1 gamma  in
                          uu____881 :: uu____883  in
                        FStar_Syntax_Util.mk_app uu____872 uu____875  in
                      FStar_Syntax_Util.abs uu____863 uu____871 ret1  in
                    let uu____885 =
                      let uu____886 = mk_all_implicit binders  in
                      let uu____890 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____886 uu____890  in
                    FStar_Syntax_Util.abs uu____885 body ret1  in
                  let c_push1 =
                    let uu____907 = mk_lid "push"  in
                    register env1 uu____907 c_push  in
                  let ret_tot_wp_a =
                    let uu____915 =
                      let uu____921 =
                        let uu____922 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.lcomp_of_comp uu____922  in
                      FStar_Util.Inl uu____921  in
                    Some uu____915  in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____950 =
                        let uu____951 =
                          let uu____961 = args_of_binders1 binders  in
                          (c, uu____961)  in
                        FStar_Syntax_Syntax.Tm_app uu____951  in
                      mk1 uu____950
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____969 =
                        let uu____970 =
                          let uu____974 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____975 =
                            let uu____977 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____977]  in
                          uu____974 :: uu____975  in
                        let uu____978 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____970 uu____978  in
                      FStar_Syntax_Syntax.mk_Total uu____969  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c" None
                        FStar_Syntax_Util.ktype
                       in
                    let uu____982 =
                      let uu____983 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____983  in
                    let uu____989 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2")) None
                         in
                      let uu____991 =
                        let uu____994 =
                          let uu____1000 =
                            let uu____1002 =
                              let uu____1005 =
                                let uu____1011 =
                                  let uu____1012 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1012  in
                                [uu____1011]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1005  in
                            [uu____1002]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1000
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____994  in
                      FStar_Syntax_Util.ascribe uu____991
                        ((FStar_Util.Inr result_comp), None)
                       in
                    FStar_Syntax_Util.abs uu____982 uu____989
                      (Some
                         (FStar_Util.Inl
                            (FStar_Syntax_Util.lcomp_of_comp result_comp)))
                     in
                  let wp_if_then_else1 =
                    let uu____1037 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1037 wp_if_then_else  in
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
                      let uu____1048 =
                        let uu____1054 =
                          let uu____1056 =
                            let uu____1059 =
                              let uu____1065 =
                                let uu____1067 =
                                  let uu____1070 =
                                    let uu____1076 =
                                      let uu____1077 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1077
                                       in
                                    [uu____1076]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1070
                                   in
                                [uu____1067]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1065
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1059  in
                          let uu____1082 =
                            let uu____1086 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1086]  in
                          uu____1056 :: uu____1082  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1054
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1048  in
                    let uu____1089 =
                      let uu____1090 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1090  in
                    FStar_Syntax_Util.abs uu____1089 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1097 = mk_lid "wp_assert"  in
                    register env1 uu____1097 wp_assert  in
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
                      let uu____1108 =
                        let uu____1114 =
                          let uu____1116 =
                            let uu____1119 =
                              let uu____1125 =
                                let uu____1127 =
                                  let uu____1130 =
                                    let uu____1136 =
                                      let uu____1137 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1137
                                       in
                                    [uu____1136]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1130
                                   in
                                [uu____1127]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1125
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1119  in
                          let uu____1142 =
                            let uu____1146 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1146]  in
                          uu____1116 :: uu____1142  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1114
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1108  in
                    let uu____1149 =
                      let uu____1150 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1150  in
                    FStar_Syntax_Util.abs uu____1149 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1157 = mk_lid "wp_assume"  in
                    register env1 uu____1157 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b" None
                        FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1166 =
                        let uu____1170 =
                          let uu____1171 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1171  in
                        [uu____1170]  in
                      let uu____1172 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1166 uu____1172  in
                    let f = FStar_Syntax_Syntax.gen_bv "f" None t_f  in
                    let body =
                      let uu____1179 =
                        let uu____1185 =
                          let uu____1187 =
                            let uu____1190 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1190  in
                          let uu____1196 =
                            let uu____1200 =
                              let uu____1203 =
                                let uu____1209 =
                                  let uu____1211 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1211]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1209
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1203  in
                            [uu____1200]  in
                          uu____1187 :: uu____1196  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1185
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1179  in
                    let uu____1218 =
                      let uu____1219 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1219  in
                    FStar_Syntax_Util.abs uu____1218 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1226 = mk_lid "wp_close"  in
                    register env1 uu____1226 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    let uu____1237 =
                      let uu____1243 =
                        let uu____1244 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1244
                         in
                      FStar_Util.Inl uu____1243  in
                    Some uu____1237  in
                  let ret_gtot_type =
                    let uu____1264 =
                      let uu____1270 =
                        let uu____1271 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1271
                         in
                      FStar_Util.Inl uu____1270  in
                    Some uu____1264  in
                  let mk_forall1 x body =
                    let uu____1291 =
                      let uu____1294 =
                        let uu____1295 =
                          let uu____1305 =
                            let uu____1307 =
                              let uu____1308 =
                                let uu____1309 =
                                  let uu____1310 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1310]  in
                                FStar_Syntax_Util.abs uu____1309 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1308  in
                            [uu____1307]  in
                          (FStar_Syntax_Util.tforall, uu____1305)  in
                        FStar_Syntax_Syntax.Tm_app uu____1295  in
                      FStar_Syntax_Syntax.mk uu____1294  in
                    uu____1291 None FStar_Range.dummyRange  in
                  let rec is_discrete t =
                    let uu____1324 =
                      let uu____1325 = FStar_Syntax_Subst.compress t  in
                      uu____1325.FStar_Syntax_Syntax.n  in
                    match uu____1324 with
                    | FStar_Syntax_Syntax.Tm_type uu____1328 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1343  ->
                              match uu____1343 with
                              | (b,uu____1347) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1348 -> true  in
                  let rec is_monotonic t =
                    let uu____1353 =
                      let uu____1354 = FStar_Syntax_Subst.compress t  in
                      uu____1354.FStar_Syntax_Syntax.n  in
                    match uu____1353 with
                    | FStar_Syntax_Syntax.Tm_type uu____1357 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1372  ->
                              match uu____1372 with
                              | (b,uu____1376) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1377 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1429 =
                      let uu____1430 = FStar_Syntax_Subst.compress t1  in
                      uu____1430.FStar_Syntax_Syntax.n  in
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
                        let a2 = (Prims.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1479 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1479
                        then
                          let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2
                             in
                          let body =
                            let uu____1482 =
                              let uu____1485 =
                                let uu____1491 =
                                  let uu____1492 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1492  in
                                [uu____1491]  in
                              FStar_Syntax_Util.mk_app x uu____1485  in
                            let uu____1493 =
                              let uu____1496 =
                                let uu____1502 =
                                  let uu____1503 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1503  in
                                [uu____1502]  in
                              FStar_Syntax_Util.mk_app y uu____1496  in
                            mk_rel1 b uu____1482 uu____1493  in
                          mk_forall1 a11 body
                        else
                          (let a11 = FStar_Syntax_Syntax.gen_bv "a1" None a2
                              in
                           let a21 = FStar_Syntax_Syntax.gen_bv "a2" None a2
                              in
                           let body =
                             let uu____1508 =
                               let uu____1509 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1512 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1509 uu____1512  in
                             let uu____1515 =
                               let uu____1516 =
                                 let uu____1519 =
                                   let uu____1525 =
                                     let uu____1526 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1526
                                      in
                                   [uu____1525]  in
                                 FStar_Syntax_Util.mk_app x uu____1519  in
                               let uu____1527 =
                                 let uu____1530 =
                                   let uu____1536 =
                                     let uu____1537 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1537
                                      in
                                   [uu____1536]  in
                                 FStar_Syntax_Util.mk_app y uu____1530  in
                               mk_rel1 b uu____1516 uu____1527  in
                             FStar_Syntax_Util.mk_imp uu____1508 uu____1515
                              in
                           let uu____1538 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1538)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___98_1559 = t1  in
                          let uu____1560 =
                            let uu____1561 =
                              let uu____1569 =
                                let uu____1570 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____1570  in
                              ([binder], uu____1569)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____1561  in
                          {
                            FStar_Syntax_Syntax.n = uu____1560;
                            FStar_Syntax_Syntax.tk =
                              (uu___98_1559.FStar_Syntax_Syntax.tk);
                            FStar_Syntax_Syntax.pos =
                              (uu___98_1559.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___98_1559.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____1582 ->
                        failwith "unhandled arrow"
                    | uu____1590 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____1605 =
                        let uu____1606 = FStar_Syntax_Subst.compress t1  in
                        uu____1606.FStar_Syntax_Syntax.n  in
                      match uu____1605 with
                      | FStar_Syntax_Syntax.Tm_type uu____1609 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____1626 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____1626
                          ->
                          let project i tuple =
                            let projector =
                              let uu____1641 =
                                let uu____1642 =
                                  FStar_Syntax_Util.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____1642 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____1641
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1")) None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, None)]
                             in
                          let uu____1663 =
                            let uu____1667 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____1672  ->
                                     match uu____1672 with
                                     | (t2,q) ->
                                         let uu____1677 = project i x  in
                                         let uu____1678 = project i y  in
                                         mk_stronger t2 uu____1677 uu____1678)
                                args
                               in
                            match uu____1667 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____1663 with
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
                                 fun uu____1734  ->
                                   match uu____1734 with
                                   | (bv,q) ->
                                       let uu____1739 =
                                         let uu____1740 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____1740  in
                                       FStar_Syntax_Syntax.gen_bv uu____1739
                                         None bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____1744 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____1744) bvs
                             in
                          let body =
                            let uu____1746 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____1747 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____1746 uu____1747  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____1750 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____1752 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____1753 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____1754 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____1752 uu____1753 uu____1754  in
                    let uu____1755 =
                      let uu____1756 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____1756  in
                    FStar_Syntax_Util.abs uu____1755 body ret_tot_type  in
                  let stronger1 =
                    let uu____1771 = mk_lid "stronger"  in
                    register env1 uu____1771 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let uu____1777 = FStar_Util.prefix gamma  in
                    match uu____1777 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k" None
                            (Prims.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____1803 =
                              FStar_Syntax_Syntax.bv_to_name (Prims.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____1803
                             in
                          let uu____1806 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____1806 with
                          | Some (FStar_Syntax_Util.QAll (binders1,[],body))
                              ->
                              let k_app =
                                let uu____1814 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____1814  in
                              let guard_free1 =
                                let uu____1821 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Syntax_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____1821  in
                              let pat =
                                let uu____1825 =
                                  let uu____1831 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____1831]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____1825
                                 in
                              let pattern_guarded_body =
                                let uu____1835 =
                                  let uu____1836 =
                                    let uu____1841 =
                                      let uu____1842 =
                                        let uu____1849 =
                                          let uu____1851 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____1851]  in
                                        [uu____1849]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____1842
                                       in
                                    (body, uu____1841)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____1836  in
                                mk1 uu____1835  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____1854 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____1857 =
                            let uu____1858 =
                              let uu____1859 =
                                let uu____1860 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____1863 =
                                  let uu____1869 = args_of_binders1 wp_args
                                     in
                                  let uu____1871 =
                                    let uu____1873 =
                                      let uu____1874 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____1874
                                       in
                                    [uu____1873]  in
                                  FStar_List.append uu____1869 uu____1871  in
                                FStar_Syntax_Util.mk_app uu____1860
                                  uu____1863
                                 in
                              FStar_Syntax_Util.mk_imp equiv uu____1859  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____1858
                             in
                          FStar_Syntax_Util.abs gamma uu____1857
                            ret_gtot_type
                           in
                        let uu____1875 =
                          let uu____1876 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____1876  in
                        FStar_Syntax_Util.abs uu____1875 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____1883 = mk_lid "wp_ite"  in
                    register env1 uu____1883 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let uu____1889 = FStar_Util.prefix gamma  in
                    match uu____1889 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x" None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____1913 =
                            let uu____1914 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (Prims.fst post)
                               in
                            let uu____1917 =
                              let uu____1923 =
                                let uu____1924 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____1924  in
                              [uu____1923]  in
                            FStar_Syntax_Util.mk_app uu____1914 uu____1917
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____1913
                           in
                        let uu____1925 =
                          let uu____1926 =
                            let uu____1930 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____1930 gamma  in
                          FStar_List.append binders uu____1926  in
                        FStar_Syntax_Util.abs uu____1925 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____1939 = mk_lid "null_wp"  in
                    register env1 uu____1939 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp = FStar_Syntax_Syntax.gen_bv "wp" None wp_a1  in
                    let body =
                      let uu____1948 =
                        let uu____1954 =
                          let uu____1956 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____1957 =
                            let uu____1959 =
                              let uu____1962 =
                                let uu____1968 =
                                  let uu____1969 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____1969  in
                                [uu____1968]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____1962
                               in
                            let uu____1970 =
                              let uu____1974 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____1974]  in
                            uu____1959 :: uu____1970  in
                          uu____1956 :: uu____1957  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1954
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____1948  in
                    let uu____1977 =
                      let uu____1978 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____1978  in
                    FStar_Syntax_Util.abs uu____1977 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____1985 = mk_lid "wp_trivial"  in
                    register env1 uu____1985 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____1990 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____1990
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____1995 =
                      let uu____1997 = FStar_ST.read sigelts  in
                      FStar_List.rev uu____1997  in
                    let uu____2002 =
                      let uu___99_2003 = ed  in
                      let uu____2004 =
                        let uu____2005 = c wp_if_then_else2  in
                        ([], uu____2005)  in
                      let uu____2007 =
                        let uu____2008 = c wp_ite2  in ([], uu____2008)  in
                      let uu____2010 =
                        let uu____2011 = c stronger2  in ([], uu____2011)  in
                      let uu____2013 =
                        let uu____2014 = c wp_close2  in ([], uu____2014)  in
                      let uu____2016 =
                        let uu____2017 = c wp_assert2  in ([], uu____2017)
                         in
                      let uu____2019 =
                        let uu____2020 = c wp_assume2  in ([], uu____2020)
                         in
                      let uu____2022 =
                        let uu____2023 = c null_wp2  in ([], uu____2023)  in
                      let uu____2025 =
                        let uu____2026 = c wp_trivial2  in ([], uu____2026)
                         in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___99_2003.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___99_2003.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___99_2003.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___99_2003.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___99_2003.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___99_2003.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___99_2003.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___99_2003.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2004;
                        FStar_Syntax_Syntax.ite_wp = uu____2007;
                        FStar_Syntax_Syntax.stronger = uu____2010;
                        FStar_Syntax_Syntax.close_wp = uu____2013;
                        FStar_Syntax_Syntax.assert_p = uu____2016;
                        FStar_Syntax_Syntax.assume_p = uu____2019;
                        FStar_Syntax_Syntax.null_wp = uu____2022;
                        FStar_Syntax_Syntax.trivial = uu____2025;
                        FStar_Syntax_Syntax.repr =
                          (uu___99_2003.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___99_2003.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___99_2003.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___99_2003.FStar_Syntax_Syntax.actions)
                      }  in
                    (uu____1995, uu____2002)))))
  
type env_ = env
let get_env : env -> FStar_TypeChecker_Env.env = fun env  -> env.env 
let set_env : env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___100_2038 = dmff_env  in
      {
        env = env';
        subst = (uu___100_2038.subst);
        tc_const = (uu___100_2038.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let uu___is_N : nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2049 -> false 
let __proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0 
let uu___is_M : nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2061 -> false 
let __proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let nm_of_comp : FStar_Syntax_Syntax.comp' -> nm =
  fun uu___86_2071  ->
    match uu___86_2071 with
    | FStar_Syntax_Syntax.Total (t,uu____2073) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___85_2082  ->
                match uu___85_2082 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2083 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2085 =
          let uu____2086 =
            let uu____2087 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2087
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2086  in
        failwith uu____2085
    | FStar_Syntax_Syntax.GTotal uu____2088 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let string_of_nm : nm -> Prims.string =
  fun uu___87_2096  ->
    match uu___87_2096 with
    | N t ->
        let uu____2098 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2098
    | M t ->
        let uu____2100 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2100
  
let is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2104,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.tk = uu____2106;
                      FStar_Syntax_Syntax.pos = uu____2107;
                      FStar_Syntax_Syntax.vars = uu____2108;_})
        -> nm_of_comp n2
    | uu____2119 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let is_monadic_comp c =
  let uu____2131 = nm_of_comp c.FStar_Syntax_Syntax.n  in
  match uu____2131 with | M uu____2132 -> true | N uu____2133 -> false 
exception Not_found 
let uu___is_Not_found : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2137 -> false
  
let double_star :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun typ  ->
    let star_once typ1 =
      let uu____2147 =
        let uu____2151 =
          let uu____2152 = FStar_Syntax_Syntax.new_bv None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2152  in
        [uu____2151]  in
      let uu____2153 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____2147 uu____2153  in
    let uu____2156 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____2156
  
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
          (let uu____2191 =
             let uu____2199 =
               let uu____2203 =
                 let uu____2206 =
                   let uu____2207 = star_type' env a  in
                   FStar_Syntax_Syntax.null_bv uu____2207  in
                 let uu____2208 = FStar_Syntax_Syntax.as_implicit false  in
                 (uu____2206, uu____2208)  in
               [uu____2203]  in
             let uu____2213 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
             (uu____2199, uu____2213)  in
           FStar_Syntax_Syntax.Tm_arrow uu____2191)

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____2246) ->
          let binders1 =
            FStar_List.map
              (fun uu____2265  ->
                 match uu____2265 with
                 | (bv,aqual) ->
                     let uu____2272 =
                       let uu___101_2273 = bv  in
                       let uu____2274 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___101_2273.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___101_2273.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____2274
                       }  in
                     (uu____2272, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____2277,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____2279);
                             FStar_Syntax_Syntax.tk = uu____2280;
                             FStar_Syntax_Syntax.pos = uu____2281;
                             FStar_Syntax_Syntax.vars = uu____2282;_})
               ->
               let uu____2299 =
                 let uu____2300 =
                   let uu____2308 =
                     let uu____2309 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____2309  in
                   (binders1, uu____2308)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____2300  in
               mk1 uu____2299
           | uu____2313 ->
               let uu____2314 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____2314 with
                | N hn ->
                    let uu____2316 =
                      let uu____2317 =
                        let uu____2325 =
                          let uu____2326 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____2326  in
                        (binders1, uu____2325)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____2317  in
                    mk1 uu____2316
                | M a ->
                    let uu____2331 =
                      let uu____2332 =
                        let uu____2340 =
                          let uu____2344 =
                            let uu____2348 =
                              let uu____2351 =
                                let uu____2352 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____2352  in
                              let uu____2353 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____2351, uu____2353)  in
                            [uu____2348]  in
                          FStar_List.append binders1 uu____2344  in
                        let uu____2360 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____2340, uu____2360)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____2332  in
                    mk1 uu____2331))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____2411 = f x  in
                    FStar_Util.string_builder_append strb uu____2411);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____2415 = f x1  in
                         FStar_Util.string_builder_append strb uu____2415))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____2417 = FStar_Syntax_Print.term_to_string t2  in
            let uu____2418 = string_of_set FStar_Syntax_Print.bv_to_string s
               in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____2417 uu____2418
             in
          let rec is_non_dependent_arrow ty n1 =
            let uu____2426 =
              let uu____2427 = FStar_Syntax_Subst.compress ty  in
              uu____2427.FStar_Syntax_Syntax.n  in
            match uu____2426 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____2442 =
                  let uu____2443 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____2443  in
                if uu____2442
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____2457 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____2457 s  in
                       let uu____2459 =
                         let uu____2460 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____2460  in
                       if uu____2459
                       then (debug1 ty1 sinter; Prims.raise Not_found)
                       else ()  in
                     let uu____2463 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____2463 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____2474  ->
                                  match uu____2474 with
                                  | (bv,uu____2480) ->
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
            | uu____2493 ->
                ((let uu____2495 = FStar_Syntax_Print.term_to_string ty  in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____2495);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____2500 =
              let uu____2501 = FStar_Syntax_Subst.compress head2  in
              uu____2501.FStar_Syntax_Syntax.n  in
            match uu____2500 with
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
                  (let uu____2505 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____2505)
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
                 | FStar_Syntax_Syntax.Tm_app uu____2518 -> true
                 | uu____2528 ->
                     ((let uu____2530 =
                         FStar_Syntax_Print.term_to_string head2  in
                       FStar_Util.print1_warning
                         "Got a term which might be a non-dependent user-defined data-type %s\n"
                         uu____2530);
                      false))
            | FStar_Syntax_Syntax.Tm_bvar _|FStar_Syntax_Syntax.Tm_name _ ->
                true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2534) ->
                is_valid_application t2
            | uu____2539 -> false  in
          let uu____2540 = is_valid_application head1  in
          if uu____2540
          then
            let uu____2541 =
              let uu____2542 =
                let uu____2552 =
                  FStar_List.map
                    (fun uu____2562  ->
                       match uu____2562 with
                       | (t2,qual) ->
                           let uu____2575 = star_type' env t2  in
                           (uu____2575, qual)) args
                   in
                (head1, uu____2552)  in
              FStar_Syntax_Syntax.Tm_app uu____2542  in
            mk1 uu____2541
          else
            (let uu____2582 =
               let uu____2583 =
                 let uu____2584 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____2584
                  in
               FStar_Errors.Err uu____2583  in
             Prims.raise uu____2582)
      | FStar_Syntax_Syntax.Tm_bvar _
        |FStar_Syntax_Syntax.Tm_name _
         |FStar_Syntax_Syntax.Tm_type _|FStar_Syntax_Syntax.Tm_fvar _ -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____2614 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____2614 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___104_2620 = env  in
                 let uu____2621 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____2621;
                   subst = (uu___104_2620.subst);
                   tc_const = (uu___104_2620.tc_const)
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
               ((let uu___105_2638 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___105_2638.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___105_2638.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____2645 =
            let uu____2646 =
              let uu____2651 = star_type' env t2  in (uu____2651, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____2646  in
          mk1 uu____2645
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,None ),something) ->
          let uu____2689 =
            let uu____2690 =
              let uu____2708 = star_type' env e  in
              let uu____2709 =
                let uu____2719 =
                  let uu____2724 = star_type' env t2  in
                  FStar_Util.Inl uu____2724  in
                (uu____2719, None)  in
              (uu____2708, uu____2709, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____2690  in
          mk1 uu____2689
      | FStar_Syntax_Syntax.Tm_ascribed uu____2746 ->
          let uu____2764 =
            let uu____2765 =
              let uu____2766 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_ascribed is outside of the definition language: %s"
                uu____2766
               in
            FStar_Errors.Err uu____2765  in
          Prims.raise uu____2764
      | FStar_Syntax_Syntax.Tm_refine uu____2767 ->
          let uu____2772 =
            let uu____2773 =
              let uu____2774 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____2774
               in
            FStar_Errors.Err uu____2773  in
          Prims.raise uu____2772
      | FStar_Syntax_Syntax.Tm_uinst uu____2775 ->
          let uu____2780 =
            let uu____2781 =
              let uu____2782 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____2782
               in
            FStar_Errors.Err uu____2781  in
          Prims.raise uu____2780
      | FStar_Syntax_Syntax.Tm_constant uu____2783 ->
          let uu____2784 =
            let uu____2785 =
              let uu____2786 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____2786
               in
            FStar_Errors.Err uu____2785  in
          Prims.raise uu____2784
      | FStar_Syntax_Syntax.Tm_match uu____2787 ->
          let uu____2803 =
            let uu____2804 =
              let uu____2805 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____2805
               in
            FStar_Errors.Err uu____2804  in
          Prims.raise uu____2803
      | FStar_Syntax_Syntax.Tm_let uu____2806 ->
          let uu____2814 =
            let uu____2815 =
              let uu____2816 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____2816
               in
            FStar_Errors.Err uu____2815  in
          Prims.raise uu____2814
      | FStar_Syntax_Syntax.Tm_uvar uu____2817 ->
          let uu____2826 =
            let uu____2827 =
              let uu____2828 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____2828
               in
            FStar_Errors.Err uu____2827  in
          Prims.raise uu____2826
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____2829 =
            let uu____2830 =
              let uu____2831 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____2831
               in
            FStar_Errors.Err uu____2830  in
          Prims.raise uu____2829
      | FStar_Syntax_Syntax.Tm_delayed uu____2832 -> failwith "impossible"

let is_monadic uu___89_2865 =
  match uu___89_2865 with
  | None  -> failwith "un-annotated lambda?!"
  | Some (FStar_Util.Inl
    { FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _;
      FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _;_})
    |Some (FStar_Util.Inr (_,flags)) ->
      FStar_All.pipe_right flags
        (FStar_Util.for_some
           (fun uu___88_2902  ->
              match uu___88_2902 with
              | FStar_Syntax_Syntax.CPS  -> true
              | uu____2903 -> false))
  
let rec is_C : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____2907 =
      let uu____2908 = FStar_Syntax_Subst.compress t  in
      uu____2908.FStar_Syntax_Syntax.n  in
    match uu____2907 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____2928 =
            let uu____2929 = FStar_List.hd args  in Prims.fst uu____2929  in
          is_C uu____2928  in
        if r
        then
          ((let uu____2941 =
              let uu____2942 =
                FStar_List.for_all
                  (fun uu____2945  ->
                     match uu____2945 with | (h,uu____2949) -> is_C h) args
                 in
              Prims.op_Negation uu____2942  in
            if uu____2941 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____2953 =
              let uu____2954 =
                FStar_List.for_all
                  (fun uu____2957  ->
                     match uu____2957 with
                     | (h,uu____2961) ->
                         let uu____2962 = is_C h  in
                         Prims.op_Negation uu____2962) args
                 in
              Prims.op_Negation uu____2954  in
            if uu____2953 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____2976 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____2976 with
         | M t1 ->
             ((let uu____2979 = is_C t1  in
               if uu____2979 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,_)
      |FStar_Syntax_Syntax.Tm_uinst (t1,_)|FStar_Syntax_Syntax.Tm_ascribed
       (t1,_,_) -> is_C t1
    | uu____3011 -> false
  
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
          let uu____3042 =
            let uu____3043 =
              let uu____3053 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____3054 =
                let uu____3058 =
                  let uu____3061 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____3061)  in
                [uu____3058]  in
              (uu____3053, uu____3054)  in
            FStar_Syntax_Syntax.Tm_app uu____3043  in
          mk1 uu____3042  in
        let uu____3069 =
          let uu____3070 = FStar_Syntax_Syntax.mk_binder p  in [uu____3070]
           in
        let uu____3071 =
          let uu____3078 =
            let uu____3084 =
              let uu____3085 =
                FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
              FStar_Syntax_Util.lcomp_of_comp uu____3085  in
            FStar_Util.Inl uu____3084  in
          Some uu____3078  in
        FStar_Syntax_Util.abs uu____3069 body uu____3071
  
let is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___90_3098  ->
    match uu___90_3098 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____3099 -> false
  
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
        let return_if uu____3243 =
          match uu____3243 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____3264 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____3265 =
                       let uu____3266 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____3266  in
                     Prims.op_Negation uu____3265)
                   in
                if uu____3264
                then
                  let uu____3267 =
                    let uu____3268 =
                      let uu____3269 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____3270 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____3271 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____3269 uu____3270 uu____3271
                       in
                    FStar_Errors.Err uu____3268  in
                  Prims.raise uu____3267
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2)|(M t1,M t2) ->
                   (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____3282 = mk_return env t1 s_e  in
                     ((M t1), uu____3282, u_e)))
               | (M t1,N t2) ->
                   let uu____3285 =
                     let uu____3286 =
                       let uu____3287 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____3288 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____3289 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____3287 uu____3288 uu____3289
                        in
                     FStar_Errors.Err uu____3286  in
                   Prims.raise uu____3285)
           in
        let ensure_m env1 e2 =
          let strip_m uu___91_3315 =
            match uu___91_3315 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____3325 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____3336 =
                let uu____3337 =
                  let uu____3340 =
                    let uu____3341 = FStar_Syntax_Print.term_to_string t  in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____3341
                     in
                  (uu____3340, (e2.FStar_Syntax_Syntax.pos))  in
                FStar_Errors.Error uu____3337  in
              Prims.raise uu____3336
          | M uu____3345 ->
              let uu____3346 = check env1 e2 context_nm  in
              strip_m uu____3346
           in
        let uu____3350 =
          let uu____3351 = FStar_Syntax_Subst.compress e  in
          uu____3351.FStar_Syntax_Syntax.n  in
        match uu____3350 with
        | FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_name _
           |FStar_Syntax_Syntax.Tm_fvar _
            |FStar_Syntax_Syntax.Tm_abs _
             |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_app _
            -> let uu____3363 = infer env e  in return_if uu____3363
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
        | FStar_Syntax_Syntax.Tm_let uu____3438 ->
            let uu____3446 =
              let uu____3447 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____3447  in
            failwith uu____3446
        | FStar_Syntax_Syntax.Tm_type uu____3451 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____3455 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____3466 ->
            let uu____3471 =
              let uu____3472 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____3472  in
            failwith uu____3471
        | FStar_Syntax_Syntax.Tm_uvar uu____3476 ->
            let uu____3485 =
              let uu____3486 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____3486  in
            failwith uu____3485
        | FStar_Syntax_Syntax.Tm_delayed uu____3490 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____3514 =
              let uu____3515 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____3515  in
            failwith uu____3514

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
      let uu____3537 =
        let uu____3538 = FStar_Syntax_Subst.compress e  in
        uu____3538.FStar_Syntax_Syntax.n  in
      match uu____3537 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,what) ->
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let env1 =
            let uu___106_3578 = env  in
            let uu____3579 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____3579;
              subst = (uu___106_3578.subst);
              tc_const = (uu___106_3578.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____3588  ->
                 match uu____3588 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___107_3596 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___107_3596.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___107_3596.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____3597 =
            FStar_List.fold_left
              (fun uu____3606  ->
                 fun uu____3607  ->
                   match (uu____3606, uu____3607) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____3635 = is_C c  in
                       if uu____3635
                       then
                         let xw =
                           let uu____3640 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "^w") None uu____3640
                            in
                         let x =
                           let uu___108_3642 = bv  in
                           let uu____3643 =
                             let uu____3646 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____3646  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___108_3642.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___108_3642.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____3643
                           }  in
                         let env3 =
                           let uu___109_3648 = env2  in
                           let uu____3649 =
                             let uu____3651 =
                               let uu____3652 =
                                 let uu____3657 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____3657)  in
                               FStar_Syntax_Syntax.NT uu____3652  in
                             uu____3651 :: (env2.subst)  in
                           {
                             env = (uu___109_3648.env);
                             subst = uu____3649;
                             tc_const = (uu___109_3648.tc_const)
                           }  in
                         let uu____3658 =
                           let uu____3660 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____3661 =
                             let uu____3663 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____3663 :: acc  in
                           uu____3660 :: uu____3661  in
                         (env3, uu____3658)
                       else
                         (let x =
                            let uu___110_3667 = bv  in
                            let uu____3668 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___110_3667.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___110_3667.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____3668
                            }  in
                          let uu____3671 =
                            let uu____3673 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____3673 :: acc  in
                          (env2, uu____3671))) (env1, []) binders1
             in
          (match uu____3597 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____3685 =
                 let check_what =
                   let uu____3697 = is_monadic what  in
                   if uu____3697 then check_m else check_n  in
                 let uu____3706 = check_what env2 body1  in
                 match uu____3706 with
                 | (t,s_body,u_body) ->
                     let uu____3716 =
                       let uu____3717 =
                         let uu____3718 = is_monadic what  in
                         if uu____3718 then M t else N t  in
                       comp_of_nm uu____3717  in
                     (uu____3716, s_body, u_body)
                  in
               (match uu____3685 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_what =
                      match what with
                      | None  -> None
                      | Some (FStar_Util.Inl lc) ->
                          let uu____3761 =
                            FStar_All.pipe_right
                              lc.FStar_Syntax_Syntax.cflags
                              (FStar_Util.for_some
                                 (fun uu___92_3763  ->
                                    match uu___92_3763 with
                                    | FStar_Syntax_Syntax.CPS  -> true
                                    | uu____3764 -> false))
                             in
                          if uu____3761
                          then
                            let double_starred_comp =
                              let uu____3772 =
                                let uu____3773 =
                                  let uu____3774 =
                                    lc.FStar_Syntax_Syntax.comp ()  in
                                  FStar_Syntax_Util.comp_result uu____3774
                                   in
                                FStar_All.pipe_left double_star uu____3773
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____3772  in
                            let flags =
                              FStar_List.filter
                                (fun uu___93_3779  ->
                                   match uu___93_3779 with
                                   | FStar_Syntax_Syntax.CPS  -> false
                                   | uu____3780 -> true)
                                lc.FStar_Syntax_Syntax.cflags
                               in
                            let uu____3781 =
                              let uu____3787 =
                                let uu____3788 =
                                  FStar_Syntax_Util.comp_set_flags
                                    double_starred_comp flags
                                   in
                                FStar_Syntax_Util.lcomp_of_comp uu____3788
                                 in
                              FStar_Util.Inl uu____3787  in
                            Some uu____3781
                          else
                            Some
                              (FStar_Util.Inl
                                 ((let uu___111_3808 = lc  in
                                   {
                                     FStar_Syntax_Syntax.eff_name =
                                       (uu___111_3808.FStar_Syntax_Syntax.eff_name);
                                     FStar_Syntax_Syntax.res_typ =
                                       (uu___111_3808.FStar_Syntax_Syntax.res_typ);
                                     FStar_Syntax_Syntax.cflags =
                                       (uu___111_3808.FStar_Syntax_Syntax.cflags);
                                     FStar_Syntax_Syntax.comp =
                                       (fun uu____3809  ->
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
                          let uu____3826 =
                            let uu____3832 =
                              let uu____3836 =
                                FStar_All.pipe_right flags
                                  (FStar_Util.for_some
                                     (fun uu___94_3838  ->
                                        match uu___94_3838 with
                                        | FStar_Syntax_Syntax.CPS  -> true
                                        | uu____3839 -> false))
                                 in
                              if uu____3836
                              then
                                let uu____3843 =
                                  FStar_List.filter
                                    (fun uu___95_3845  ->
                                       match uu___95_3845 with
                                       | FStar_Syntax_Syntax.CPS  -> false
                                       | uu____3846 -> true) flags
                                   in
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  uu____3843)
                              else (lid, flags)  in
                            FStar_Util.Inr uu____3832  in
                          Some uu____3826
                       in
                    let uu____3858 =
                      let comp1 =
                        let uu____3870 = is_monadic what  in
                        let uu____3871 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____3870 uu____3871
                         in
                      let uu____3872 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1), None)
                         in
                      (uu____3872,
                        (Some
                           (FStar_Util.Inl
                              (FStar_Syntax_Util.lcomp_of_comp comp1))))
                       in
                    (match uu____3858 with
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
                FStar_Syntax_Syntax.ty = uu____3950;
                FStar_Syntax_Syntax.p = uu____3951;_};
            FStar_Syntax_Syntax.fv_delta = uu____3952;
            FStar_Syntax_Syntax.fv_qual = uu____3953;_}
          ->
          let uu____3959 =
            let uu____3962 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left Prims.fst uu____3962  in
          (match uu____3959 with
           | (uu____3978,t) ->
               let uu____3980 =
                 let uu____3981 = normalize1 t  in N uu____3981  in
               (uu____3980, e, e))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____3998 = check_n env head1  in
          (match uu____3998 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____4012 =
                   let uu____4013 = FStar_Syntax_Subst.compress t  in
                   uu____4013.FStar_Syntax_Syntax.n  in
                 match uu____4012 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____4016 -> true
                 | uu____4024 -> false  in
               let rec flatten1 t =
                 let uu____4036 =
                   let uu____4037 = FStar_Syntax_Subst.compress t  in
                   uu____4037.FStar_Syntax_Syntax.n  in
                 match uu____4036 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____4049);
                                FStar_Syntax_Syntax.tk = uu____4050;
                                FStar_Syntax_Syntax.pos = uu____4051;
                                FStar_Syntax_Syntax.vars = uu____4052;_})
                     when is_arrow t1 ->
                     let uu____4069 = flatten1 t1  in
                     (match uu____4069 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4121,uu____4122)
                     -> flatten1 e1
                 | uu____4151 ->
                     let uu____4152 =
                       let uu____4153 =
                         let uu____4154 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____4154
                          in
                       FStar_Errors.Err uu____4153  in
                     Prims.raise uu____4152
                  in
               let uu____4162 = flatten1 t_head  in
               (match uu____4162 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____4207 =
                          let uu____4208 =
                            let uu____4209 = FStar_Util.string_of_int n1  in
                            let uu____4213 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____4219 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____4209 uu____4213 uu____4219
                             in
                          FStar_Errors.Err uu____4208  in
                        Prims.raise uu____4207)
                     else ();
                     (let uu____4224 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____4224 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____4251 args1 =
                            match uu____4251 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____4294 =
                                       let uu____4295 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____4295.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____4294
                                 | (binders3,[]) ->
                                     let uu____4314 =
                                       let uu____4315 =
                                         let uu____4318 =
                                           let uu____4319 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____4319
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____4318
                                          in
                                       uu____4315.FStar_Syntax_Syntax.n  in
                                     (match uu____4314 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____4335 =
                                            let uu____4336 =
                                              let uu____4337 =
                                                let uu____4345 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____4345)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____4337
                                               in
                                            mk1 uu____4336  in
                                          N uu____4335
                                      | uu____4349 -> failwith "wat?")
                                 | ([],uu____4350::uu____4351) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____4376)::binders3,(arg,uu____4379)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____4413 = FStar_List.splitAt n' binders1  in
                          (match uu____4413 with
                           | (binders2,uu____4430) ->
                               let uu____4443 =
                                 let uu____4453 =
                                   FStar_List.map2
                                     (fun uu____4473  ->
                                        fun uu____4474  ->
                                          match (uu____4473, uu____4474) with
                                          | ((bv,uu____4491),(arg,q)) ->
                                              let uu____4498 =
                                                let uu____4499 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____4499.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____4498 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____4509 ->
                                                   let arg1 = (arg, q)  in
                                                   (arg1, [arg1])
                                               | uu____4522 ->
                                                   let uu____4523 =
                                                     check_n env arg  in
                                                   (match uu____4523 with
                                                    | (uu____4534,s_arg,u_arg)
                                                        ->
                                                        let uu____4537 =
                                                          let uu____4541 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____4541
                                                          then
                                                            let uu____4545 =
                                                              let uu____4548
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____4548, q)
                                                               in
                                                            [uu____4545;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____4537))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____4453  in
                               (match uu____4443 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____4595 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____4601 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____4595, uu____4601)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,_)
        |FStar_Syntax_Syntax.Tm_meta (e1,_)|FStar_Syntax_Syntax.Tm_ascribed
         (e1,_,_) -> infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____4679 = let uu____4680 = env.tc_const c  in N uu____4680
             in
          (uu____4679, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____4681 ->
          let uu____4689 =
            let uu____4690 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____4690  in
          failwith uu____4689
      | FStar_Syntax_Syntax.Tm_type uu____4694 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____4698 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____4709 ->
          let uu____4714 =
            let uu____4715 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____4715  in
          failwith uu____4714
      | FStar_Syntax_Syntax.Tm_uvar uu____4719 ->
          let uu____4728 =
            let uu____4729 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____4729  in
          failwith uu____4728
      | FStar_Syntax_Syntax.Tm_delayed uu____4733 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4757 =
            let uu____4758 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____4758  in
          failwith uu____4757

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
          let uu____4796 = check_n env e0  in
          match uu____4796 with
          | (uu____4803,s_e0,u_e0) ->
              let uu____4806 =
                let uu____4824 =
                  FStar_List.map
                    (fun b  ->
                       let uu____4857 = FStar_Syntax_Subst.open_branch b  in
                       match uu____4857 with
                       | (pat,None ,body) ->
                           let env1 =
                             let uu___112_4889 = env  in
                             let uu____4890 =
                               let uu____4891 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____4891
                                in
                             {
                               env = uu____4890;
                               subst = (uu___112_4889.subst);
                               tc_const = (uu___112_4889.tc_const)
                             }  in
                           let uu____4893 = f env1 body  in
                           (match uu____4893 with
                            | (nm,s_body,u_body) ->
                                (nm, (pat, None, (s_body, u_body, body))))
                       | uu____4942 ->
                           Prims.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____4824  in
              (match uu____4806 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____5007 = FStar_List.hd nms  in
                     match uu____5007 with | M t1|N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___96_5010  ->
                          match uu___96_5010 with
                          | M uu____5011 -> true
                          | uu____5012 -> false) nms
                      in
                   let uu____5013 =
                     let uu____5036 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____5088  ->
                              match uu____5088 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false )|(M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____5184 =
                                         check env original_body (M t2)  in
                                       (match uu____5184 with
                                        | (uu____5207,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____5236,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____5036  in
                   (match uu____5013 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____5355  ->
                                 match uu____5355 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____5396 =
                                         let uu____5397 =
                                           let uu____5407 =
                                             let uu____5411 =
                                               let uu____5414 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____5415 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____5414, uu____5415)  in
                                             [uu____5411]  in
                                           (s_body, uu____5407)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____5397
                                          in
                                       mk1 uu____5396  in
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
                            let uu____5437 =
                              let uu____5438 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____5438]  in
                            let uu____5439 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            let uu____5441 =
                              let uu____5448 =
                                let uu____5454 =
                                  let uu____5455 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0
                                     in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5455
                                   in
                                FStar_Util.Inl uu____5454  in
                              Some uu____5448  in
                            FStar_Syntax_Util.abs uu____5437 uu____5439
                              uu____5441
                             in
                          let t1_star =
                            let uu____5469 =
                              let uu____5473 =
                                let uu____5474 =
                                  FStar_Syntax_Syntax.new_bv None p_type  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____5474
                                 in
                              [uu____5473]  in
                            let uu____5475 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____5469 uu____5475  in
                          let uu____5478 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e, ((FStar_Util.Inl t1_star), None),
                                   None))
                             in
                          let uu____5508 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____5478, uu____5508)
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
                           let uu____5522 =
                             let uu____5525 =
                               let uu____5526 =
                                 let uu____5544 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____5544,
                                   ((FStar_Util.Inl t1_star), None), None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____5526  in
                             mk1 uu____5525  in
                           let uu____5571 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____5522, uu____5571))))

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
              let uu____5614 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____5614]  in
            let uu____5615 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____5615 with
            | (x_binders1,e21) ->
                let uu____5623 = infer env e1  in
                (match uu____5623 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____5634 = is_C t1  in
                       if uu____5634
                       then
                         let uu___113_5635 = binding  in
                         let uu____5636 =
                           let uu____5639 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____5639  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___113_5635.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___113_5635.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____5636;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___113_5635.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___113_5635.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding  in
                     let env1 =
                       let uu___114_5642 = env  in
                       let uu____5643 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___115_5644 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___115_5644.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___115_5644.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____5643;
                         subst = (uu___114_5642.subst);
                         tc_const = (uu___114_5642.tc_const)
                       }  in
                     let uu____5645 = proceed env1 e21  in
                     (match uu____5645 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___116_5656 = binding  in
                            let uu____5657 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___116_5656.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___116_5656.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____5657;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___116_5656.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___116_5656.FStar_Syntax_Syntax.lbdef)
                            }  in
                          let uu____5660 =
                            let uu____5663 =
                              let uu____5664 =
                                let uu____5672 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___117_5677 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___117_5677.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___117_5677.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___117_5677.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___117_5677.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____5672)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5664  in
                            mk1 uu____5663  in
                          let uu____5678 =
                            let uu____5681 =
                              let uu____5682 =
                                let uu____5690 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___118_5695 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___118_5695.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___118_5695.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___118_5695.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___118_5695.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5690)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5682  in
                            mk1 uu____5681  in
                          (nm_rec, uu____5660, uu____5678))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___119_5704 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___119_5704.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___119_5704.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Syntax_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___119_5704.FStar_Syntax_Syntax.lbdef)
                       }  in
                     let env1 =
                       let uu___120_5706 = env  in
                       let uu____5707 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___121_5708 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___121_5708.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___121_5708.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____5707;
                         subst = (uu___120_5706.subst);
                         tc_const = (uu___120_5706.tc_const)
                       }  in
                     let uu____5709 = ensure_m env1 e21  in
                     (match uu____5709 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''" None p_type  in
                          let s_e21 =
                            let uu____5726 =
                              let uu____5727 =
                                let uu____5737 =
                                  let uu____5741 =
                                    let uu____5744 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____5745 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____5744, uu____5745)  in
                                  [uu____5741]  in
                                (s_e2, uu____5737)  in
                              FStar_Syntax_Syntax.Tm_app uu____5727  in
                            mk1 uu____5726  in
                          let s_e22 =
                            let uu____5754 =
                              let uu____5761 =
                                let uu____5767 =
                                  let uu____5768 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0
                                     in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5768
                                   in
                                FStar_Util.Inl uu____5767  in
                              Some uu____5761  in
                            FStar_Syntax_Util.abs x_binders1 s_e21 uu____5754
                             in
                          let body =
                            let uu____5782 =
                              let uu____5783 =
                                let uu____5793 =
                                  let uu____5797 =
                                    let uu____5800 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____5800)  in
                                  [uu____5797]  in
                                (s_e1, uu____5793)  in
                              FStar_Syntax_Syntax.Tm_app uu____5783  in
                            mk1 uu____5782  in
                          let uu____5808 =
                            let uu____5809 =
                              let uu____5810 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____5810]  in
                            let uu____5811 =
                              let uu____5818 =
                                let uu____5824 =
                                  let uu____5825 =
                                    FStar_Syntax_Syntax.mk_Total
                                      FStar_Syntax_Util.ktype0
                                     in
                                  FStar_Syntax_Util.lcomp_of_comp uu____5825
                                   in
                                FStar_Util.Inl uu____5824  in
                              Some uu____5818  in
                            FStar_Syntax_Util.abs uu____5809 body uu____5811
                             in
                          let uu____5836 =
                            let uu____5839 =
                              let uu____5840 =
                                let uu____5848 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___122_5853 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___122_5853.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___122_5853.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___122_5853.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___122_5853.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____5848)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____5840  in
                            mk1 uu____5839  in
                          ((M t2), uu____5808, uu____5836)))

and check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5862 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos
           in
        N uu____5862  in
      let uu____5867 = check env e mn  in
      match uu____5867 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5877 -> failwith "[check_n]: impossible"

and check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____5890 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
            e.FStar_Syntax_Syntax.pos
           in
        M uu____5890  in
      let uu____5895 = check env e mn  in
      match uu____5895 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____5905 -> failwith "[check_m]: impossible"

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
        (let uu____5927 =
           let uu____5928 = is_C c  in Prims.op_Negation uu____5928  in
         if uu____5927 then failwith "not a C" else ());
        (let mk1 x = FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos
            in
         let uu____5940 =
           let uu____5941 = FStar_Syntax_Subst.compress c  in
           uu____5941.FStar_Syntax_Syntax.n  in
         match uu____5940 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____5960 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____5960 with
              | (wp_head,wp_args) ->
                  ((let uu____5987 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____6000 =
                           let uu____6001 =
                             FStar_Syntax_Util.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____6001
                            in
                         Prims.op_Negation uu____6000)
                       in
                    if uu____5987 then failwith "mismatch" else ());
                   (let uu____6010 =
                      let uu____6011 =
                        let uu____6021 =
                          FStar_List.map2
                            (fun uu____6031  ->
                               fun uu____6032  ->
                                 match (uu____6031, uu____6032) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____6055 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____6055
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____6058 = print_implicit q
                                            in
                                         let uu____6059 = print_implicit q'
                                            in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b"
                                           uu____6058 uu____6059)
                                      else ();
                                      (let uu____6061 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____6061, q)))) args wp_args
                           in
                        (head1, uu____6021)  in
                      FStar_Syntax_Syntax.Tm_app uu____6011  in
                    mk1 uu____6010)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____6083 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____6083 with
              | (binders_orig,comp1) ->
                  let uu____6088 =
                    let uu____6096 =
                      FStar_List.map
                        (fun uu____6110  ->
                           match uu____6110 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____6123 = is_C h  in
                               if uu____6123
                               then
                                 let w' =
                                   let uu____6130 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "-w'") None uu____6130
                                    in
                                 let uu____6131 =
                                   let uu____6135 =
                                     let uu____6139 =
                                       let uu____6142 =
                                         let uu____6143 =
                                           let uu____6144 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____6144  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____6143
                                          in
                                       (uu____6142, q)  in
                                     [uu____6139]  in
                                   (w', q) :: uu____6135  in
                                 (w', uu____6131)
                               else
                                 (let x =
                                    let uu____6156 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "-x") None uu____6156
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____6096  in
                  (match uu____6088 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____6186 =
                           let uu____6188 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____6188
                            in
                         FStar_Syntax_Subst.subst_comp uu____6186 comp1  in
                       let app =
                         let uu____6192 =
                           let uu____6193 =
                             let uu____6203 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____6210 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____6211 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____6210, uu____6211)) bvs
                                in
                             (wp, uu____6203)  in
                           FStar_Syntax_Syntax.Tm_app uu____6193  in
                         mk1 uu____6192  in
                       let comp3 =
                         let uu____6216 = type_of_comp comp2  in
                         let uu____6217 = is_monadic_comp comp2  in
                         trans_G env uu____6216 uu____6217 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____6219,uu____6220) ->
             trans_F_ env e wp
         | uu____6249 -> failwith "impossible trans_F_")

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
            let uu____6264 =
              let uu____6265 = star_type' env h  in
              let uu____6268 =
                let uu____6274 =
                  let uu____6277 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____6277)  in
                [uu____6274]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Syntax_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____6265;
                FStar_Syntax_Syntax.effect_args = uu____6268;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____6264
          else
            (let uu____6283 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____6283)

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
    fun t  -> let uu____6294 = n env.env t  in star_type' env uu____6294
  
let star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> let uu____6306 = n env.env t  in check_n env uu____6306
  
let trans_F :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____6316 = n env.env c  in
        let uu____6317 = n env.env wp  in trans_F_ env uu____6316 uu____6317
  